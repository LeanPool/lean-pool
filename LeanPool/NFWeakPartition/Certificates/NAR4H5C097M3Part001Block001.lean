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

/-! Certificates from `AlphaSupport.NAR4H5C097M3Part001Stage1`. -/


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

@[expose]
noncomputable def nb097_alpha_dummy_000 (C : Class) (F : Class) : Var :=
  (freshVar ((F).fv ∪ (C).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_001 (C : Class) (F : Class) : Var :=
  (freshVar ((F).fv ∪ (C).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_002 (C : Class) (F : Class) : Var :=
  (freshVar (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_003 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (({ m } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv)
    0)

@[expose]
noncomputable def nb097_alpha_dummy_004 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
          (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
              (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
              (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                  (Class.cv (nb097_alpha_dummy_000 C F))))))
          (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_005 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
          (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
              (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
              (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                  (Class.cv (nb097_alpha_dummy_000 C F))))))
          (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_006 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
            (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
              (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
          (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_007 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
            (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
              (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
          (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_008 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
      ((Class.cv (nb097_alpha_dummy_000 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_009 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
      ((Class.cv (nb097_alpha_dummy_000 C F))).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_010 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_011 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_012 (C : Class) (F : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_013 (k : Var) (m : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl
          (Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c)))))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_014 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_008 C F)
          (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
            (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
              (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪
      ((Class.cab (nb097_alpha_dummy_008 C F)
          (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
            (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
              (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_015 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_010 k m)
          (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
            (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
              (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪
      ((Class.cab (nb097_alpha_dummy_010 k m) (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
            (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
              (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_016 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_017 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_018 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_019 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_020 (C : Class) (F : Class) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪
      ((Class.cv (nb097_alpha_dummy_016 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_021 (k : Var) (m : Var) : Var :=
  (freshVar (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪
        ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪
      ((Class.cv (nb097_alpha_dummy_018 k m))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_022 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_023 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_024 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb097_alpha_dummy_025 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_026 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
noncomputable def nb097_alpha_dummy_027 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
noncomputable def nb097_alpha_dummy_028 (C : Class) (F : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
          (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪
      ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
          (Class.cv (nb097_alpha_dummy_024 C F)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_029 (k : Var) (m : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
          (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪
      ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
          (Class.cv (nb097_alpha_dummy_027 k m)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_030 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
      ((Class.cv (nb097_alpha_dummy_024 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_031 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
      ((Class.cv (nb097_alpha_dummy_027 k m))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_032 (C : Class) (F : Class) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪
      ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_033 (k : Var) (m : Var) : Var :=
  (freshVar (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪
      ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_034 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
      ((Class.cv (nb097_alpha_dummy_023 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_035 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
      ((Class.cv (nb097_alpha_dummy_026 k m))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_036 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪
      ((Class.cv (nb097_alpha_dummy_024 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_037 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪
      ((Class.cv (nb097_alpha_dummy_027 k m))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_038 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_008 C F)
          (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
            (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
              (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F)
          (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
            (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
              (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_039 (k : Var) (m : Var) : Var :=
  (freshVar (((Class.cab (nb097_alpha_dummy_010 k m)
          (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
            (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
              (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m)
          (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
            (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
              (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                (syn_csn (syn_c0c))))))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_040 (C : Class) (F : Class) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_041 (k : Var) (m : Var) : Var :=
  (freshVar (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪
      ((syn_ccompl (syn_csn (syn_c0c)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_042 (C : Class) (F : Class) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪
      ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_043 (k : Var) (m : Var) : Var :=
  (freshVar (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪
      ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_044 (C : Class) (F : Class) : Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_002 C F))).fv) 0)

@[expose]
noncomputable def nb097_alpha_dummy_045 (C : Class) (k : Var) (m : Var) (F : Class) :
    Var :=
  (freshVar (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) 0)

theorem nb097_fresh_000 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ∉
      (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
            (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                  (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                    (Class.cv (nb097_alpha_dummy_000 C F))))))
            (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_004] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
            (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                  (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                    (Class.cv (nb097_alpha_dummy_000 C F))))))
            (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
      0

theorem nb097_fresh_001 (C : Class) (F : Class) :
    (nb097_alpha_dummy_005 C F) ∉
      (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
            (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                  (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                    (Class.cv (nb097_alpha_dummy_000 C F))))))
            (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_005] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
            (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                  (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                    (Class.cv (nb097_alpha_dummy_000 C F))))))
            (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
      1

theorem nb097_distinct_002 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ≠ (nb097_alpha_dummy_005 C F) := by
  simpa only [nb097_alpha_dummy_004, nb097_alpha_dummy_005] using
    (freshVar_injective (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
            (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                  (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                    (Class.cv (nb097_alpha_dummy_000 C F))))))
            (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_fresh_003 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_006 C k m F) ∉
      (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
              (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
            (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_006] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
              (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
            (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
      0

theorem nb097_fresh_004 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_007 C k m F) ∉
      (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
              (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
            (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_007] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
              (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
            (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
      1

theorem nb097_distinct_005 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_006 C k m F) ≠ (nb097_alpha_dummy_007 C k m F) := by
  simpa only [nb097_alpha_dummy_006, nb097_alpha_dummy_007] using
    (freshVar_injective (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
              (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
            (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_fresh_006 (C : Class) (F : Class) :
    (nb097_alpha_dummy_038 C F) ∉
      (((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_038] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb097_fresh_007 (C : Class) (F : Class) :
    (nb097_alpha_dummy_014 C F) ∉
      (((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪
        ((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_014] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪
        ((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv)
      0

theorem nb097_fresh_008 (k : Var) (m : Var) :
    (nb097_alpha_dummy_039 k m) ∉
      (((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_039] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c))))))).fv)
      0

theorem nb097_fresh_009 (k : Var) (m : Var) :
    (nb097_alpha_dummy_015 k m) ∉
      (((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪
        ((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_015] using
    freshVar_not_mem
      (((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪
        ((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv)
      0

theorem nb097_fresh_010 (C : Class) (F : Class) :
    (nb097_alpha_dummy_008 C F) ∉
      (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_008] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv)
      0

theorem nb097_fresh_011 (C : Class) (F : Class) :
    (nb097_alpha_dummy_009 C F) ∉
      (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_009] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv)
      1

theorem nb097_distinct_012 (C : Class) (F : Class) :
    (nb097_alpha_dummy_008 C F) ≠ (nb097_alpha_dummy_009 C F) := by
  simpa only [nb097_alpha_dummy_008, nb097_alpha_dummy_009] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_013 (C : Class) (F : Class) :
    (nb097_alpha_dummy_044 C F) ∉ (((Class.cv (nb097_alpha_dummy_002 C F))).fv) := by
  simpa only [nb097_alpha_dummy_044] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_002 C F))).fv) 0

theorem nb097_fresh_014 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_045 C k m F) ∉ (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_045] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) 0

theorem nb097_fresh_015 (C : Class) (F : Class) :
    (nb097_alpha_dummy_016 C F) ∉ (((Class.cv (nb097_alpha_dummy_009 C F))).fv) := by
  simpa only [nb097_alpha_dummy_016] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 0

theorem nb097_fresh_016 (C : Class) (F : Class) :
    (nb097_alpha_dummy_017 C F) ∉ (((Class.cv (nb097_alpha_dummy_009 C F))).fv) := by
  simpa only [nb097_alpha_dummy_017] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_009 C F))).fv) 1

theorem nb097_distinct_017 (C : Class) (F : Class) :
    (nb097_alpha_dummy_016 C F) ≠ (nb097_alpha_dummy_017 C F) := by
  simpa only [nb097_alpha_dummy_016, nb097_alpha_dummy_017] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_009 C F))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb097_fresh_018 (k : Var) (m : Var) :
    (nb097_alpha_dummy_018 k m) ∉ (((Class.cv (nb097_alpha_dummy_011 k m))).fv) := by
  simpa only [nb097_alpha_dummy_018] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 0

theorem nb097_fresh_019 (k : Var) (m : Var) :
    (nb097_alpha_dummy_019 k m) ∉ (((Class.cv (nb097_alpha_dummy_011 k m))).fv) := by
  simpa only [nb097_alpha_dummy_019] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_011 k m))).fv) 1

theorem nb097_distinct_020 (k : Var) (m : Var) :
    (nb097_alpha_dummy_018 k m) ≠ (nb097_alpha_dummy_019 k m) := by
  simpa only [nb097_alpha_dummy_018, nb097_alpha_dummy_019] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_011 k m))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb097_fresh_021 (C : Class) (F : Class) :
    (nb097_alpha_dummy_022 C F) ∉
      (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb097_alpha_dummy_022] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 0

theorem nb097_fresh_022 (C : Class) (F : Class) :
    (nb097_alpha_dummy_023 C F) ∉
      (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb097_alpha_dummy_023] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 1

theorem nb097_fresh_023 (C : Class) (F : Class) :
    (nb097_alpha_dummy_024 C F) ∉
      (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb097_alpha_dummy_024] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) 2

theorem nb097_distinct_024 (C : Class) (F : Class) :
    (nb097_alpha_dummy_022 C F) ≠ (nb097_alpha_dummy_023 C F) := by
  simpa only [nb097_alpha_dummy_022, nb097_alpha_dummy_023] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_distinct_025 (C : Class) (F : Class) :
    (nb097_alpha_dummy_022 C F) ≠ (nb097_alpha_dummy_024 C F) := by
  simpa only [nb097_alpha_dummy_022, nb097_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb097_distinct_026 (C : Class) (F : Class) :
    (nb097_alpha_dummy_023 C F) ≠ (nb097_alpha_dummy_024 C F) := by
  simpa only [nb097_alpha_dummy_023, nb097_alpha_dummy_024] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb097_fresh_027 (k : Var) (m : Var) :
    (nb097_alpha_dummy_025 k m) ∉
      (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb097_alpha_dummy_025] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 0

theorem nb097_fresh_028 (k : Var) (m : Var) :
    (nb097_alpha_dummy_026 k m) ∉
      (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb097_alpha_dummy_026] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 1

theorem nb097_fresh_029 (k : Var) (m : Var) :
    (nb097_alpha_dummy_027 k m) ∉
      (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) :=
  by
  simpa only [nb097_alpha_dummy_027] using
    freshVar_not_mem (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) 2

theorem nb097_distinct_030 (k : Var) (m : Var) :
    (nb097_alpha_dummy_025 k m) ≠ (nb097_alpha_dummy_026 k m) := by
  simpa only [nb097_alpha_dummy_025, nb097_alpha_dummy_026] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb097_distinct_031 (k : Var) (m : Var) :
    (nb097_alpha_dummy_025 k m) ≠ (nb097_alpha_dummy_027 k m) := by
  simpa only [nb097_alpha_dummy_025, nb097_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb097_distinct_032 (k : Var) (m : Var) :
    (nb097_alpha_dummy_026 k m) ≠ (nb097_alpha_dummy_027 k m) := by
  simpa only [nb097_alpha_dummy_026, nb097_alpha_dummy_027] using
    (freshVar_injective (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb097_fresh_033 (C : Class) (F : Class) :
    (nb097_alpha_dummy_034 C F) ∉
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_023 C F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_034] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_023 C F))).fv)
      0

theorem nb097_fresh_034 (C : Class) (F : Class) :
    (nb097_alpha_dummy_030 C F) ∉
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_030] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv)
      0

theorem nb097_fresh_035 (C : Class) (F : Class) :
    (nb097_alpha_dummy_036 C F) ∉
      (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_036] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv)
      0

theorem nb097_fresh_036 (k : Var) (m : Var) :
    (nb097_alpha_dummy_035 k m) ∉
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_026 k m))).fv) :=
  by
  simpa only [nb097_alpha_dummy_035] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_026 k m))).fv)
      0

theorem nb097_fresh_037 (k : Var) (m : Var) :
    (nb097_alpha_dummy_031 k m) ∉
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv) :=
  by
  simpa only [nb097_alpha_dummy_031] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv)
      0

theorem nb097_fresh_038 (k : Var) (m : Var) :
    (nb097_alpha_dummy_037 k m) ∉
      (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv) :=
  by
  simpa only [nb097_alpha_dummy_037] using
    freshVar_not_mem
      (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv)
      0

theorem nb097_fresh_039 (k : Var) (m : Var) :
    (nb097_alpha_dummy_010 k m) ∉ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  simpa only [nb097_alpha_dummy_010] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 0

theorem nb097_fresh_040 (k : Var) (m : Var) :
    (nb097_alpha_dummy_011 k m) ∉ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) := by
  simpa only [nb097_alpha_dummy_011] using
    freshVar_not_mem (((Class.cv m)).fv ∪ ((Class.cv k)).fv) 1

theorem nb097_distinct_041 (k : Var) (m : Var) :
    (nb097_alpha_dummy_010 k m) ≠ (nb097_alpha_dummy_011 k m) := by
  simpa only [nb097_alpha_dummy_010, nb097_alpha_dummy_011] using
    (freshVar_injective (((Class.cv m)).fv ∪ ((Class.cv k)).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_042 (C : Class) (F : Class) :
    (nb097_alpha_dummy_020 C F) ∉
      (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪
        ((Class.cv (nb097_alpha_dummy_016 C F))).fv) :=
  by
  simpa only [nb097_alpha_dummy_020] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪
        ((Class.cv (nb097_alpha_dummy_016 C F))).fv)
      0

theorem nb097_fresh_043 (k : Var) (m : Var) :
    (nb097_alpha_dummy_021 k m) ∉
      (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪
        ((Class.cv (nb097_alpha_dummy_018 k m))).fv) :=
  by
  simpa only [nb097_alpha_dummy_021] using
    freshVar_not_mem
      (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪
        ((Class.cv (nb097_alpha_dummy_018 k m))).fv)
      0

theorem nb097_fresh_044 (C : Class) (F : Class) :
    (nb097_alpha_dummy_012 C F) ∉
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_012] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb097_fresh_045 (k : Var) (m : Var) :
    (nb097_alpha_dummy_013 k m) ∉
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_013] using
    freshVar_not_mem
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                    (syn_csn (syn_c0c)))))))).fv)
      0

theorem nb097_fresh_046 (C : Class) (F : Class) :
    (nb097_alpha_dummy_032 C F) ∉
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_032] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv)
      0

theorem nb097_fresh_047 (k : Var) (m : Var) :
    (nb097_alpha_dummy_033 k m) ∉
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_033] using
    freshVar_not_mem
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv)
      0

theorem nb097_fresh_048 (C : Class) (F : Class) :
    (nb097_alpha_dummy_040 C F) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb097_fresh_049 (k : Var) (m : Var) :
    (nb097_alpha_dummy_041 k m) ∉
      (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_041] using
    freshVar_not_mem
      (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv)
      0

theorem nb097_fresh_050 (C : Class) (F : Class) :
    (nb097_alpha_dummy_028 C F) ∉
      (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_028] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv)
      0

theorem nb097_fresh_051 (k : Var) (m : Var) :
    (nb097_alpha_dummy_029 k m) ∉
      (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_029] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv)
      0

theorem nb097_fresh_052 (C : Class) (F : Class) :
    (nb097_alpha_dummy_042 C F) ∉
      (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪
        ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_042] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪
        ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv)
      0

theorem nb097_fresh_053 (k : Var) (m : Var) :
    (nb097_alpha_dummy_043 k m) ∉
      (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪
        ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) :=
  by
  simpa only [nb097_alpha_dummy_043] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪
        ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv)
      0

theorem nb097_fresh_054 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∉ ((F).fv ∪ (C).fv) := by
  simpa only [nb097_alpha_dummy_000] using freshVar_not_mem ((F).fv ∪ (C).fv) 0

theorem nb097_fresh_055 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∉ ((F).fv ∪ (C).fv) := by
  simpa only [nb097_alpha_dummy_001] using freshVar_not_mem ((F).fv ∪ (C).fv) 1

theorem nb097_distinct_056 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_001 C F) := by
  simpa only [nb097_alpha_dummy_000, nb097_alpha_dummy_001] using
    (freshVar_injective ((F).fv ∪ (C).fv) (i := 0) (j := 1) (by decide))

theorem nb097_fresh_057 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∉
      (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F)))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_002] using
    freshVar_not_mem
      (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F)))))).fv)
      0

theorem nb097_fresh_058 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∉
      (({ m } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C)
              (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv) :=
  by
  simpa only [nb097_alpha_dummy_003] using
    freshVar_not_mem
      (({ m } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv)
      0

theorem nb097_support_mem_0000 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∈
      (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0001 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∈
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_008 C F) from (by
          unfold nb097_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_009 C F) from (by
            unfold nb097_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0002 (k : Var) (m : Var) :
    m ∈ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0003 (k : Var) (m : Var) :
    m ∈
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb097_alpha_dummy_010 k m) from (by
          unfold nb097_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb097_alpha_dummy_011 k m) from (by
            unfold nb097_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0004 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∈
      (((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv ∪
        ((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_008 C F) from (by
          unfold nb097_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097_alpha_dummy_001 C F) ≠ (nb097_alpha_dummy_009 C F) from (by
            unfold nb097_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0000 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0005 (k : Var) (m : Var) :
    m ∈
      (((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv ∪
        ((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show m ≠ (nb097_alpha_dummy_010 k m) from (by
          unfold nb097_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show m ≠ (nb097_alpha_dummy_011 k m) from (by
            unfold nb097_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0002 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0006 (C : Class) (F : Class) :
    (nb097_alpha_dummy_009 C F) ∈ (((Class.cv (nb097_alpha_dummy_009 C F))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0007 (k : Var) (m : Var) :
    (nb097_alpha_dummy_011 k m) ∈ (((Class.cv (nb097_alpha_dummy_011 k m))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0008 (C : Class) (F : Class) :
    (nb097_alpha_dummy_016 C F) ∈
      (((Wff.classMem (Class.cv (nb097_alpha_dummy_016 C F)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb097_alpha_dummy_016 C F)) (syn_c1c))).fv ∪
        ((Class.cv (nb097_alpha_dummy_016 C F))).fv) :=
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

theorem nb097_support_mem_0009 (k : Var) (m : Var) :
    (nb097_alpha_dummy_018 k m) ∈
      (((Wff.classMem (Class.cv (nb097_alpha_dummy_018 k m)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb097_alpha_dummy_018 k m)) (syn_c1c))).fv ∪
        ((Class.cv (nb097_alpha_dummy_018 k m))).fv) :=
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

theorem nb097_support_mem_0010 (C : Class) (F : Class) :
    (nb097_alpha_dummy_016 C F) ∈
      (((Class.cv (nb097_alpha_dummy_016 C F))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0011 (k : Var) (m : Var) :
    (nb097_alpha_dummy_018 k m) ∈
      (((Class.cv (nb097_alpha_dummy_018 k m))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0012 (C : Class) (F : Class) :
    (nb097_alpha_dummy_023 C F) ∈
      (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0013 (k : Var) (m : Var) :
    (nb097_alpha_dummy_026 k m) ∈
      (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0014 (C : Class) (F : Class) :
    (nb097_alpha_dummy_023 C F) ∈
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0015 (k : Var) (m : Var) :
    (nb097_alpha_dummy_026 k m) ∈
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0016 (C : Class) (F : Class) :
    (nb097_alpha_dummy_024 C F) ∈
      (((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_023 C F))
            (Class.cv (nb097_alpha_dummy_024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0017 (k : Var) (m : Var) :
    (nb097_alpha_dummy_027 k m) ∈
      (((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv ∪
        ((syn_cnin (Class.cv (nb097_alpha_dummy_026 k m))
            (Class.cv (nb097_alpha_dummy_027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0018 (C : Class) (F : Class) :
    (nb097_alpha_dummy_024 C F) ∈
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0019 (k : Var) (m : Var) :
    (nb097_alpha_dummy_027 k m) ∈
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0020 (C : Class) (F : Class) :
    (nb097_alpha_dummy_023 C F) ∈
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0021 (k : Var) (m : Var) :
    (nb097_alpha_dummy_026 k m) ∈
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0022 (C : Class) (F : Class) :
    (nb097_alpha_dummy_023 C F) ∈
      (((Class.cv (nb097_alpha_dummy_023 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_023 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0023 (k : Var) (m : Var) :
    (nb097_alpha_dummy_026 k m) ∈
      (((Class.cv (nb097_alpha_dummy_026 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_026 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0024 (C : Class) (F : Class) :
    (nb097_alpha_dummy_024 C F) ∈
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_023 C F)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_024 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0025 (k : Var) (m : Var) :
    (nb097_alpha_dummy_027 k m) ∈
      (((syn_ccompl (Class.cv (nb097_alpha_dummy_026 k m)))).fv ∪
        ((syn_ccompl (Class.cv (nb097_alpha_dummy_027 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0026 (C : Class) (F : Class) :
    (nb097_alpha_dummy_024 C F) ∈
      (((Class.cv (nb097_alpha_dummy_024 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_024 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0027 (k : Var) (m : Var) :
    (nb097_alpha_dummy_027 k m) ∈
      (((Class.cv (nb097_alpha_dummy_027 k m))).fv ∪
        ((Class.cv (nb097_alpha_dummy_027 k m))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0028 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∈
      (((Class.cv (nb097_alpha_dummy_001 C F))).fv ∪
        ((Class.cv (nb097_alpha_dummy_000 C F))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0029 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∈
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_001 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_008 C F)
              (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
                (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_008 C F) from (by
          unfold nb097_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_009 C F) from (by
            unfold nb097_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0030 (k : Var) (m : Var) :
    k ∈ (((Class.cv m)).fv ∪ ((Class.cv k)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0031 (k : Var) (m : Var) :
    k ∈
      (((syn_ccompl (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv m)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb097_alpha_dummy_010 k m)
              (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
                (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                  (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show k ≠ (nb097_alpha_dummy_010 k m) from (by
          unfold nb097_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show k ≠ (nb097_alpha_dummy_011 k m) from (by
            unfold nb097_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0032 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∈
      (((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_008 C F)
            (syn_wrex (nb097_alpha_dummy_009 C F) (Class.cv (nb097_alpha_dummy_000 C F))
              (Wff.classEq (Class.cv (nb097_alpha_dummy_008 C F))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_008 C F) from (by
          unfold nb097_alpha_dummy_008;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb097_alpha_dummy_000 C F) ≠ (nb097_alpha_dummy_009 C F) from (by
            unfold nb097_alpha_dummy_009;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0028 C F) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0033 (k : Var) (m : Var) :
    k ∈
      (((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb097_alpha_dummy_010 k m)
            (syn_wrex (nb097_alpha_dummy_011 k m) (Class.cv k)
              (Wff.classEq (Class.cv (nb097_alpha_dummy_010 k m))
                (syn_cun (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show k ≠ (nb097_alpha_dummy_010 k m) from (by
          unfold nb097_alpha_dummy_010;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show k ≠ (nb097_alpha_dummy_011 k m) from (by
            unfold nb097_alpha_dummy_011;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb097_support_mem_0030 k m) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb097_support_mem_0034 (C : Class) (F : Class) :
    (nb097_alpha_dummy_009 C F) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_009 C F))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0035 (k : Var) (m : Var) :
    (nb097_alpha_dummy_011 k m) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb097_alpha_dummy_011 k m))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0036 (C : Class) (F : Class) :
    (nb097_alpha_dummy_009 C F) ∈
      (((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv ∪
        ((syn_cphi (Class.cv (nb097_alpha_dummy_009 C F)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0037 (k : Var) (m : Var) :
    (nb097_alpha_dummy_011 k m) ∈
      (((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv ∪
        ((syn_cphi (Class.cv (nb097_alpha_dummy_011 k m)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0038 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∈ (((Class.cv (nb097_alpha_dummy_002 C F))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_support_mem_0039 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∈ (((Class.cv (nb097_alpha_dummy_003 C k m F))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb097_focused_notmem_0000 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∉ C.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 1 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb097_focused_notmem_0001 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∉ F.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 1 ∉ F.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb097_wpp_notmem_0000 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_001, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0000 C F) (nb097_focused_notmem_0001 C F))

theorem nb097_wpp_notmem_0001 (C : Class) (m : Var) (F : Class) (dv_C_m : m ∉ C.fv)
    (dv_F_m : m ∉ F.fv) : m ∉ ((syn_cwppcand F C)).fv := by
  simpa only [fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro dv_C_m dv_F_m)

theorem nb097_focused_notmem_0002 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∉ C.fv :=
  by
  change
    freshVar
        (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
              (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                  (Class.cv (nb097_alpha_dummy_000 C F)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
      (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
        (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
          (Class.cv (nb097_alpha_dummy_000 C F))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  left
  exact hu


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

theorem nb097_focused_notmem_0003 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∉ F.fv :=
  by
  change
    freshVar
        (({(nb097_alpha_dummy_001 C F)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
              (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                  (Class.cv (nb097_alpha_dummy_000 C F)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
      (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
        (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
          (Class.cv (nb097_alpha_dummy_000 C F))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb097_wpp_notmem_0002 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_002, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0002 C F) (nb097_focused_notmem_0003 C F))

theorem nb097_focused_notmem_0004 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∉ C.fv :=
  by
  change
    freshVar
        (({ m } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
              (syn_wral k (syn_cwppcand F C)
                (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv m) (syn_cwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb097_focused_notmem_0005 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∉ F.fv :=
  by
  change
    freshVar
        (({ m } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
              (syn_wral k (syn_cwppcand F C)
                (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv m) (syn_cwppcand F C)]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cwppcand F C]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb097_wpp_notmem_0003 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_003, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0004 C k m F) (nb097_focused_notmem_0005 C k m F))

theorem nb097_focused_notmem_0006 (C : Class) (F : Class) :
    (nb097_alpha_dummy_005 C F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
              (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                  (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                  (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                    (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                      (Class.cv (nb097_alpha_dummy_000 C F))))))
              (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
        1 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_002 C F)
      (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0002 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097_alpha_dummy_001 C F)
        (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0000 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0007 (C : Class) (F : Class) :
    (nb097_alpha_dummy_005 C F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
              (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                  (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                  (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                    (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                      (Class.cv (nb097_alpha_dummy_000 C F))))))
              (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_002 C F)
      (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0003 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097_alpha_dummy_001 C F)
        (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0001 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0004 (C : Class) (F : Class) :
    (nb097_alpha_dummy_005 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_005, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0006 C F) (nb097_focused_notmem_0007 C F))

theorem nb097_focused_notmem_0008 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) : (nb097_alpha_dummy_007 C k m F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
                (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                  (syn_wral k (syn_cwppcand F C)
                    (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
              (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
        1 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_003 C k m F)
      (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0004 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_C_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0009 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_F_m : m ∉ F.fv) : (nb097_alpha_dummy_007 C k m F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
                (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                  (syn_wral k (syn_cwppcand F C)
                    (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
              (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
        1 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_003 C k m F)
      (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0005 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_F_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0005 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    (nb097_alpha_dummy_007 C k m F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_007, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0008 C k m F dv_C_m)
      (nb097_focused_notmem_0009 C k m F dv_F_m))

theorem nb097_focused_notmem_0010 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
              (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                  (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                  (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                    (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                      (Class.cv (nb097_alpha_dummy_000 C F))))))
              (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_002 C F)
      (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0002 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097_alpha_dummy_001 C F)
        (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0000 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0011 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_002 C F) (Wff.classEq
              (Class.cab (nb097_alpha_dummy_001 C F) (syn_wa
                  (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
                  (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
                    (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                      (Class.cv (nb097_alpha_dummy_000 C F))))))
              (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_002 C F)
      (Wff.classEq (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0003 C F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab (nb097_alpha_dummy_001 C F)
          (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
            (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
              (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
                (Class.cv (nb097_alpha_dummy_000 C F))))))
        (syn_csn (Class.cv (nb097_alpha_dummy_002 C F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab (nb097_alpha_dummy_001 C F)
        (syn_wa (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F)))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => ((nb097_focused_notmem_0001 C F)) (h_eq ▸ hu)
    · rw [fv_syn_wa
          (Wff.classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C))
          (syn_wral (nb097_alpha_dummy_000 C F) (syn_cwppcand F C)
            (syn_wbr (Class.cv (nb097_alpha_dummy_001 C F)) (syn_clec)
              (Class.cv (nb097_alpha_dummy_000 C F))))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv (nb097_alpha_dummy_001 C F)) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0006 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_004, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0010 C F) (nb097_focused_notmem_0011 C F))

theorem nb097_focused_notmem_0012 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) : (nb097_alpha_dummy_006 C k m F) ∉ C.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
                (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                  (syn_wral k (syn_cwppcand F C)
                    (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
              (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
        0 ∉
      C.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_003 C k m F)
      (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0004 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_C_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      left
      exact hu

theorem nb097_focused_notmem_0013 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_F_m : m ∉ F.fv) : (nb097_alpha_dummy_006 C k m F) ∉ F.fv :=
  by
  change
    freshVar
        (((Class.cab (nb097_alpha_dummy_003 C k m F) (Wff.classEq (Class.cab m
                (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
                  (syn_wral k (syn_cwppcand F C)
                    (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
              (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))))).fv)
        0 ∉
      F.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_class_cab (nb097_alpha_dummy_003 C k m F)
      (Wff.classEq (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F))))]
  rw [Finset.mem_erase]
  constructor
  · exact fun h_eq => ((nb097_focused_notmem_0005 C k m F)) (h_eq ▸ hu)
  · rw [fv_wff_classEq
        (Class.cab m (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))))
        (syn_csn (Class.cv (nb097_alpha_dummy_003 C k m F)))]
    rw [Finset.mem_union]
    left
    rw [fv_class_cab m
        (syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k))))]
    rw [Finset.mem_erase]
    constructor
    · exact fun h_eq => (dv_F_m) (h_eq ▸ hu)
    · rw [fv_syn_wa (Wff.classMem (Class.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (Class.cv m) (syn_clec) (Class.cv k)))]
      rw [Finset.mem_union]
      left
      rw [fv_wff_classMem (Class.cv m) (syn_cwppcand F C)]
      rw [Finset.mem_union]
      right
      rw [fv_syn_cwppcand F C]
      rw [Finset.mem_union]
      right
      exact hu

theorem nb097_wpp_notmem_0007 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    (nb097_alpha_dummy_006 C k m F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_006, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0012 C k m F dv_C_m)
      (nb097_focused_notmem_0013 C k m F dv_F_m))

theorem nb097_compact_envfresh_0000 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    TEnvFresh
      [((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      ((syn_cwppcand F C)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0000 C F)
      (nb097_wpp_notmem_0001 C m F dv_C_m dv_F_m)
      (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F)
        (nb097_wpp_notmem_0002 C F) (nb097_wpp_notmem_0003 C k m F)
        (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F)
          (nb097_wpp_notmem_0004 C F) (nb097_wpp_notmem_0005 C k m F dv_C_m dv_F_m)
          (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F) (nb097_alpha_dummy_006 C k m F)
            (nb097_wpp_notmem_0006 C F) (nb097_wpp_notmem_0007 C k m F dv_C_m dv_F_m)
            (TEnvFresh.nil ((syn_cwppcand F C)).fv)))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C097M3Part001Stage2`. -/


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

@[expose]
noncomputable def nb097_wpp_refl_0000 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_m : m ∉ C.fv) (dv_F_m : m ∉ F.fv) :
    TReflOn
      [((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      ((syn_cwppcand F C)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0000 C k m F dv_C_m dv_F_m)

theorem nb097_focused_notmem_0014 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∉ C.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb097_focused_notmem_0015 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∉ F.fv :=
  by
  change freshVar ((F).fv ∪ (C).fv) 0 ∉ F.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb097_wpp_notmem_0008 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∉ ((syn_cwppcand F C)).fv := by
  simpa only [nb097_alpha_dummy_000, fv_syn_cwppcand, Finset.mem_union, not_or] using
    (And.intro (nb097_focused_notmem_0014 C F) (nb097_focused_notmem_0015 C F))

theorem nb097_wpp_notmem_0009 (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv)
    (dv_F_k : k ∉ F.fv) : k ∉ ((syn_cwppcand F C)).fv := by
  simpa only [fv_syn_cwppcand, Finset.mem_union, not_or] using (And.intro dv_C_k dv_F_k)

theorem nb097_compact_envfresh_0001 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) :
    TEnvFresh
      [((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      ((syn_cwppcand F C)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb097_alpha_dummy_000 C F) k (nb097_wpp_notmem_0008 C F)
      (nb097_wpp_notmem_0009 C k F dv_C_k dv_F_k)
      (TEnvFresh.consFresh (nb097_alpha_dummy_001 C F) m (nb097_wpp_notmem_0000 C F)
        (nb097_wpp_notmem_0001 C m F dv_C_m dv_F_m)
        (TEnvFresh.consFresh (nb097_alpha_dummy_002 C F) (nb097_alpha_dummy_003 C k m F)
          (nb097_wpp_notmem_0002 C F) (nb097_wpp_notmem_0003 C k m F)
          (TEnvFresh.consFresh (nb097_alpha_dummy_005 C F) (nb097_alpha_dummy_007 C k m F)
            (nb097_wpp_notmem_0004 C F) (nb097_wpp_notmem_0005 C k m F dv_C_m dv_F_m)
            (TEnvFresh.consFresh (nb097_alpha_dummy_004 C F)
              (nb097_alpha_dummy_006 C k m F) (nb097_wpp_notmem_0006 C F)
              (nb097_wpp_notmem_0007 C k m F dv_C_m dv_F_m)
              (TEnvFresh.nil ((syn_cwppcand F C)).fv))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C097M3Part001Stage3`. -/


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

@[expose]
noncomputable def nb097_wpp_refl_0001 (C : Class) (k : Var) (m : Var) (F : Class)
    (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) :
    TReflOn
      [((nb097_alpha_dummy_000 C F), k), ((nb097_alpha_dummy_001 C F), m),
        ((nb097_alpha_dummy_002 C F), (nb097_alpha_dummy_003 C k m F)),
        ((nb097_alpha_dummy_005 C F), (nb097_alpha_dummy_007 C k m F)),
        ((nb097_alpha_dummy_004 C F), (nb097_alpha_dummy_006 C k m F))]
      ((syn_cwppcand F C)).fv :=
  TEnvFresh.reflOn (nb097_compact_envfresh_0001 C k m F dv_C_k dv_C_m dv_F_k dv_F_m)

theorem nb097_compact_fv_empty_0020 (C : Class) (F : Class) :
    (nb097_alpha_dummy_000 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0021 (k : Var) : k ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0022 (C : Class) (F : Class) :
    (nb097_alpha_dummy_001 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0023 (m : Var) : m ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0024 (C : Class) (F : Class) :
    (nb097_alpha_dummy_002 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0025 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_003 C k m F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0026 (C : Class) (F : Class) :
    (nb097_alpha_dummy_005 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0027 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_007 C k m F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0028 (C : Class) (F : Class) :
    (nb097_alpha_dummy_004 C F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb097_compact_fv_empty_0029 (C : Class) (k : Var) (m : Var) (F : Class) :
    (nb097_alpha_dummy_006 C k m F) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
