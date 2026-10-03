/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! Freshness and support lemmas for finite-type alpha renaming. -/


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

/-! Shared freshness facts and the four alpha-certificate subtrees for finite types. -/


namespace FiniteTypeAlpha

@[expose]
def alpha_dummy_000 (M : Class) : Var :=
  (freshVar ((M).fv) 0)

@[expose]
def alpha_dummy_001 (M : Class) : Var :=
  (freshVar ((M).fv) 1)

@[expose]
def alpha_dummy_002 (M : Class) : Var :=
  (freshVar (((Wff.classEq M (syn_c0))).fv ∪ ((syn_c0)).fv ∪ ((syn_cio (alpha_dummy_001 M)
          (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
            (syn_wrex (alpha_dummy_000 M) M
              (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                (Class.cv (alpha_dummy_001 M))))))).fv) 0)

@[expose]
def alpha_dummy_003 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Wff.classEq M (syn_c0))).fv ∪ ((syn_c0)).fv ∪ ((syn_cio n
          (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
            (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))).fv) 0)

@[expose]
def alpha_dummy_004 : Var :=
  (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪
      ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)

@[expose]
def alpha_dummy_005 : Var :=
  (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)

@[expose]
def alpha_dummy_006 : Var :=
  (freshVar ((∅ : Finset Var)) 0)

@[expose]
def alpha_dummy_007 : Var :=
  (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)

@[expose]
def alpha_dummy_008 (M : Class) : Var :=
  (freshVar (({(alpha_dummy_001 M)} : Finset Var) ∪
      ((syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
          (syn_wrex (alpha_dummy_000 M) M
            (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
              (Class.cv (alpha_dummy_001 M)))))).fv) 0)

@[expose]
def alpha_dummy_009 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (({ n } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
          (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n))))).fv) 0)

@[expose]
def alpha_dummy_010 (M : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_008 M) (Wff.classEq (Class.cab (alpha_dummy_001 M)
            (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
              (syn_wrex (alpha_dummy_000 M) M
                (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                  (Class.cv (alpha_dummy_001 M))))))
          (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv) 0)

@[expose]
def alpha_dummy_011 (M : Class) : Var :=
  (freshVar (((Class.cab (alpha_dummy_008 M) (Wff.classEq (Class.cab (alpha_dummy_001 M)
            (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
              (syn_wrex (alpha_dummy_000 M) M
                (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                  (Class.cv (alpha_dummy_001 M))))))
          (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv) 1)

@[expose]
def alpha_dummy_012 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq (Class.cab n
            (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
              (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
          (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv) 0)

@[expose]
def alpha_dummy_013 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq (Class.cab n
            (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
              (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
          (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv) 1)

@[expose]
def alpha_dummy_014 : Var :=
  (freshVar ((∅ : Finset Var)) 1)

@[expose]
def alpha_dummy_015 : Var :=
  (freshVar (((Class.cab alpha_dummy_006
        (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_006))
          (syn_wral alpha_dummy_014 (Class.cv alpha_dummy_006)
            (Wff.classMem (syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))
              (Class.cv alpha_dummy_006)))))).fv) 0)

@[expose]
def alpha_dummy_016 : Var :=
  (freshVar (((Class.cab alpha_dummy_006
        (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_006))
          (syn_wral alpha_dummy_014 (Class.cv alpha_dummy_006)
            (Wff.classMem (syn_cplc (Class.cv alpha_dummy_014) (syn_c1c))
              (Class.cv alpha_dummy_006)))))).fv) 1)

@[expose]
def alpha_dummy_017 : Var :=
  (freshVar (((syn_c0)).fv) 0)

@[expose]
def alpha_dummy_018 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_019 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 1)

@[expose]
def alpha_dummy_020 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) 2)

@[expose]
def alpha_dummy_021 : Var :=
  (freshVar (((Class.cv alpha_dummy_014)).fv) 0)

@[expose]
def alpha_dummy_022 : Var :=
  (freshVar (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv ∪
      ((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) 0)

@[expose]
def alpha_dummy_023 : Var :=
  (freshVar (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_020)).fv) 0)

@[expose]
def alpha_dummy_024 : Var :=
  (freshVar (((syn_ccompl (Class.cv alpha_dummy_019))).fv ∪
      ((syn_ccompl (Class.cv alpha_dummy_020))).fv) 0)

@[expose]
def alpha_dummy_025 : Var :=
  (freshVar (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_019)).fv) 0)

@[expose]
def alpha_dummy_026 : Var :=
  (freshVar (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) 0)

@[expose]
def alpha_dummy_027 (M : Class) : Var :=
  (freshVar (((syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))).fv) 0)

@[expose]
def alpha_dummy_028 (a : Var) : Var :=
  (freshVar (((syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))).fv ∪
      ((syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))).fv) 0)

@[expose]
def alpha_dummy_029 (M : Class) : Var :=
  (freshVar (((syn_cpw (Class.cv (alpha_dummy_000 M)))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_030 (a : Var) : Var :=
  (freshVar (((syn_cpw (Class.cv a))).fv ∪ ((syn_c1c)).fv) 0)

@[expose]
def alpha_dummy_031 (M : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_000 M))).fv) 0)

@[expose]
def alpha_dummy_032 (a : Var) : Var :=
  (freshVar (((Class.cv a)).fv) 0)

@[expose]
def alpha_dummy_033 (M : Class) : Var :=
  (freshVar (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv ∪
      ((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv) 0)

@[expose]
def alpha_dummy_034 (a : Var) : Var :=
  (freshVar (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv ∪
      ((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv) 0)

@[expose]
def alpha_dummy_035 (M : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_031 M))).fv ∪ ((Class.cv (alpha_dummy_000 M))).fv) 0)

@[expose]
def alpha_dummy_036 (a : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_032 a))).fv ∪ ((Class.cv a)).fv) 0)

@[expose]
def alpha_dummy_037 (M : Class) : Var :=
  (freshVar (((Class.cv (alpha_dummy_008 M))).fv) 0)

@[expose]
def alpha_dummy_038 (n : Var) (M : Class) (a : Var) : Var :=
  (freshVar (((Class.cv (alpha_dummy_009 n M a))).fv) 0)

theorem fresh_003 (M : Class) :
    (alpha_dummy_010 M) ∉
      (((Class.cab (alpha_dummy_008 M) (Wff.classEq (Class.cab (alpha_dummy_001 M)
              (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
                (syn_wrex (alpha_dummy_000 M) M
                  (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                    (Class.cv (alpha_dummy_001 M))))))
            (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alpha_dummy_008 M) (Wff.classEq (Class.cab (alpha_dummy_001 M)
              (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
                (syn_wrex (alpha_dummy_000 M) M
                  (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                    (Class.cv (alpha_dummy_001 M))))))
            (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv)
      0

theorem fresh_004 (M : Class) :
    (alpha_dummy_011 M) ∉
      (((Class.cab (alpha_dummy_008 M) (Wff.classEq (Class.cab (alpha_dummy_001 M)
              (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
                (syn_wrex (alpha_dummy_000 M) M
                  (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                    (Class.cv (alpha_dummy_001 M))))))
            (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alpha_dummy_008 M) (Wff.classEq (Class.cab (alpha_dummy_001 M)
              (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
                (syn_wrex (alpha_dummy_000 M) M
                  (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                    (Class.cv (alpha_dummy_001 M))))))
            (syn_csn (Class.cv (alpha_dummy_008 M)))))).fv)
      1

theorem fresh_006 (n : Var) (M : Class) (a : Var) :
    (alpha_dummy_012 n M a) ∉
      (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq (Class.cab n
              (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
                (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
            (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq (Class.cab n
              (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
                (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
            (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv)
      0

theorem fresh_007 (n : Var) (M : Class) (a : Var) :
    (alpha_dummy_013 n M a) ∉
      (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq (Class.cab n
              (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
                (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
            (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Class.cab (alpha_dummy_009 n M a) (Wff.classEq (Class.cab n
              (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
                (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))
            (syn_csn (Class.cv (alpha_dummy_009 n M a)))))).fv)
      1

theorem fresh_025 (M : Class) :
    (alpha_dummy_002 M) ∉
      (((Wff.classEq M (syn_c0))).fv ∪ ((syn_c0)).fv ∪ ((syn_cio (alpha_dummy_001 M)
            (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
              (syn_wrex (alpha_dummy_000 M) M
                (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                  (Class.cv (alpha_dummy_001 M))))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Wff.classEq M (syn_c0))).fv ∪ ((syn_c0)).fv ∪ ((syn_cio (alpha_dummy_001 M)
            (syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
              (syn_wrex (alpha_dummy_000 M) M
                (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                  (Class.cv (alpha_dummy_001 M))))))).fv)
      0

theorem fresh_026 (n : Var) (M : Class) (a : Var) :
    (alpha_dummy_003 n M a) ∉
      (((Wff.classEq M (syn_c0))).fv ∪ ((syn_c0)).fv ∪ ((syn_cio n
            (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
              (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (((Wff.classEq M (syn_c0))).fv ∪ ((syn_c0)).fv ∪ ((syn_cio n
            (syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
              (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n)))))).fv)
      0

theorem fresh_039 (M : Class) : (alpha_dummy_000 M) ∉ ((M).fv) := by
  exact freshVar_not_mem ((M).fv) 0

theorem fresh_040 (M : Class) : (alpha_dummy_001 M) ∉ ((M).fv) := by
  exact freshVar_not_mem ((M).fv) 1

theorem fresh_042 (M : Class) :
    (alpha_dummy_008 M) ∉
      (({(alpha_dummy_001 M)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
            (syn_wrex (alpha_dummy_000 M) M
              (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                (Class.cv (alpha_dummy_001 M)))))).fv) :=
  by
  exact
    freshVar_not_mem
      (({(alpha_dummy_001 M)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv (alpha_dummy_001 M)) (syn_cnnc))
            (syn_wrex (alpha_dummy_000 M) M
              (Wff.classMem (syn_cpw1 (Class.cv (alpha_dummy_000 M)))
                (Class.cv (alpha_dummy_001 M)))))).fv)
      0

theorem fresh_043 (n : Var) (M : Class) (a : Var) :
    (alpha_dummy_009 n M a) ∉
      (({ n } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
            (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n))))).fv) :=
  by
  exact
    freshVar_not_mem
      (({ n } : Finset Var) ∪ ((syn_wa (Wff.classMem (Class.cv n) (syn_cnnc))
            (syn_wrex a M (Wff.classMem (syn_cpw1 (Class.cv a)) (Class.cv n))))).fv)
      0

theorem support_part_0000 : alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0000 :
    alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv ∪ ((syn_c1c)).fv) := by
  exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0000)

theorem support_part_0001 : alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0001 : alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv) := by
  exact support_part_0001

theorem support_part_0002 :
    alpha_dummy_019 ∈
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    true_or]

theorem support_mem_0002 :
    alpha_dummy_019 ∈
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) support_part_0002)

theorem support_part_0003 : alpha_dummy_019 ∈ (((Class.cv alpha_dummy_019)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0003 :
    alpha_dummy_019 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
  by exact (Finset.mem_union_left (((Class.cv alpha_dummy_020)).fv) support_part_0003)

theorem support_part_0004 :
    alpha_dummy_020 ∈
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    or_true]

theorem support_mem_0004 :
    alpha_dummy_020 ∈
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((syn_cnin (Class.cv alpha_dummy_019) (Class.cv alpha_dummy_020))).fv) support_part_0004)

theorem support_part_0005 : alpha_dummy_020 ∈ (((Class.cv alpha_dummy_020)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0005 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
  by exact (Finset.mem_union_right (((Class.cv alpha_dummy_019)).fv) support_part_0005)

theorem support_part_0006 :
    alpha_dummy_019 ∈ (((syn_ccompl (Class.cv alpha_dummy_019))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]

theorem support_mem_0006 :
    alpha_dummy_019 ∈
      (((syn_ccompl (Class.cv alpha_dummy_019))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_020))).fv) :=
  by
  exact
    (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_020))).fv) support_part_0006)

theorem support_part_0007 : alpha_dummy_019 ∈ (((Class.cv alpha_dummy_019)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0007 :
    alpha_dummy_019 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_019)).fv) :=
  by exact (Finset.mem_union_left (((Class.cv alpha_dummy_019)).fv) support_part_0007)

theorem support_part_0008 :
    alpha_dummy_020 ∈ (((syn_ccompl (Class.cv alpha_dummy_020))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]

theorem support_mem_0008 :
    alpha_dummy_020 ∈
      (((syn_ccompl (Class.cv alpha_dummy_019))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_020))).fv) :=
  by
  exact
    (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_019))).fv) support_part_0008)

theorem support_part_0009 : alpha_dummy_020 ∈ (((Class.cv alpha_dummy_020)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0009 :
    alpha_dummy_020 ∈
      (((Class.cv alpha_dummy_020)).fv ∪ ((Class.cv alpha_dummy_020)).fv) :=
  by exact (Finset.mem_union_left (((Class.cv alpha_dummy_020)).fv) support_part_0009)

theorem support_part_0010 (M : Class) :
    (alpha_dummy_031 M) ∈
      (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    true_or]

theorem support_mem_0010 (M : Class) :
    (alpha_dummy_031 M) ∈
      (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv)
      (support_part_0010 M))

theorem support_part_0011 (a : Var) :
    (alpha_dummy_032 a) ∈ (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    true_or]

theorem support_mem_0011 (a : Var) :
    (alpha_dummy_032 a) ∈
      (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv) :=
  by
  exact
    (Finset.mem_union_left (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv)
      (support_part_0011 a))

theorem support_part_0012 (M : Class) :
    (alpha_dummy_031 M) ∈ (((Class.cv (alpha_dummy_031 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0012 (M : Class) :
    (alpha_dummy_031 M) ∈
      (((Class.cv (alpha_dummy_031 M))).fv ∪ ((Class.cv (alpha_dummy_000 M))).fv) :=
  by
  exact
    (Finset.mem_union_left (((Class.cv (alpha_dummy_000 M))).fv) (support_part_0012 M))

theorem support_part_0013 (a : Var) :
    (alpha_dummy_032 a) ∈ (((Class.cv (alpha_dummy_032 a))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0013 (a : Var) :
    (alpha_dummy_032 a) ∈ (((Class.cv (alpha_dummy_032 a))).fv ∪ ((Class.cv a)).fv) := by
  exact (Finset.mem_union_left (((Class.cv a)).fv) (support_part_0013 a))

theorem support_part_0014 (M : Class) :
    (alpha_dummy_000 M) ∈
      (((syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c, fv_syn_cnin,
    fv_syn_cpw, eq_self, true_or]

theorem support_mem_0014 (M : Class) :
    (alpha_dummy_000 M) ∈
      (((syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))).fv) :=
  by
  exact
    (Finset.mem_union_left (((syn_cnin (syn_cpw (Class.cv (alpha_dummy_000 M))) (syn_c1c))).fv)
      (support_part_0014 M))

theorem support_part_0015 (a : Var) :
    a ∈ (((syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))).fv) := by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c, fv_syn_cnin,
    fv_syn_cpw, eq_self, true_or]

theorem support_mem_0015 (a : Var) :
    a ∈
      (((syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))).fv) :=
  by
  exact
    (Finset.mem_union_left (((syn_cnin (syn_cpw (Class.cv a)) (syn_c1c))).fv)
      (support_part_0015 a))

theorem support_part_0016 (M : Class) :
    (alpha_dummy_000 M) ∈ (((syn_cpw (Class.cv (alpha_dummy_000 M)))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]

theorem support_mem_0016 (M : Class) :
    (alpha_dummy_000 M) ∈
      (((syn_cpw (Class.cv (alpha_dummy_000 M)))).fv ∪ ((syn_c1c)).fv) :=
  by exact (Finset.mem_union_left (((syn_c1c)).fv) (support_part_0016 M))

theorem support_part_0017 (a : Var) : a ∈ (((syn_cpw (Class.cv a))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]

theorem support_mem_0017 (a : Var) : a ∈ (((syn_cpw (Class.cv a))).fv ∪ ((syn_c1c)).fv) :=
  by exact (Finset.mem_union_left (((syn_c1c)).fv) (support_part_0017 a))

theorem support_part_0018 (M : Class) :
    (alpha_dummy_000 M) ∈ (((Class.cv (alpha_dummy_000 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0018 (M : Class) :
    (alpha_dummy_000 M) ∈ (((Class.cv (alpha_dummy_000 M))).fv) := by
  exact (support_part_0018 M)

theorem support_part_0019 (a : Var) : a ∈ (((Class.cv a)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0019 (a : Var) : a ∈ (((Class.cv a)).fv) := by
  exact (support_part_0019 a)

theorem support_part_0020 (M : Class) :
    (alpha_dummy_000 M) ∈
      (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv) :=
  by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    or_true]

theorem support_mem_0020 (M : Class) :
    (alpha_dummy_000 M) ∈
      (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv) :=
  by
  exact
    (Finset.mem_union_left
      (((syn_cnin (Class.cv (alpha_dummy_031 M)) (Class.cv (alpha_dummy_000 M)))).fv)
      (support_part_0020 M))

theorem support_part_0021 (a : Var) :
    a ∈ (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv) := by
  simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
    or_true]

theorem support_mem_0021 (a : Var) :
    a ∈
      (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv ∪
        ((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv) :=
  by
  exact
    (Finset.mem_union_left (((syn_cnin (Class.cv (alpha_dummy_032 a)) (Class.cv a))).fv)
      (support_part_0021 a))

theorem support_part_0022 (M : Class) :
    (alpha_dummy_000 M) ∈ (((Class.cv (alpha_dummy_000 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0022 (M : Class) :
    (alpha_dummy_000 M) ∈
      (((Class.cv (alpha_dummy_031 M))).fv ∪ ((Class.cv (alpha_dummy_000 M))).fv) :=
  by
  exact
    (Finset.mem_union_right (((Class.cv (alpha_dummy_031 M))).fv) (support_part_0022 M))

theorem support_part_0023 (a : Var) : a ∈ (((Class.cv a)).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0023 (a : Var) :
    a ∈ (((Class.cv (alpha_dummy_032 a))).fv ∪ ((Class.cv a)).fv) := by
  exact
    (Finset.mem_union_right (((Class.cv (alpha_dummy_032 a))).fv) (support_part_0023 a))

theorem support_part_0024 (M : Class) :
    (alpha_dummy_008 M) ∈ (((Class.cv (alpha_dummy_008 M))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0024 (M : Class) :
    (alpha_dummy_008 M) ∈ (((Class.cv (alpha_dummy_008 M))).fv) := by
  exact (support_part_0024 M)

theorem support_part_0025 (n : Var) (M : Class) (a : Var) :
    (alpha_dummy_009 n M a) ∈ (((Class.cv (alpha_dummy_009 n M a))).fv) := by
  simp only [Finset.mem_singleton, fv_class_cv, eq_self]

theorem support_mem_0025 (n : Var) (M : Class) (a : Var) :
    (alpha_dummy_009 n M a) ∈ (((Class.cv (alpha_dummy_009 n M a))).fv) := by
  exact (support_part_0025 n M a)

/-- Predicate whose restricted existential retains every free parameter variable. -/
@[expose]
def finitePredicate (n : Var) (M : Class) (a : Var) : Wff :=
  syn_wa (.classMem (.cv n) syn_cnnc)
    (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))

/-- The singleton-encoding class used in the finite-type alpha certificate. -/
@[expose]
def codingClass (outer n : Var) (M : Class) (a : Var) : Class :=
  .cab outer (.classEq (.cab n (finitePredicate n M a)) (syn_csn (.cv outer)))

theorem parameter_subset_predicate (n : Var) (M : Class) (a : Var) (ha : a ∉ M.fv) :
    M.fv ⊆ (finitePredicate n M a).fv :=
  by
  rw [finitePredicate, fv_syn_wa, fv_syn_wrex]
  intro u hu
  exact
    Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hu), hu⟩))

theorem parameter_subset_codingClass (outer n : Var) (M : Class) (a : Var) (ha : a ∉ M.fv)
    (hn : n ∉ M.fv) (houter : outer ∉ ({ n } ∪ (finitePredicate n M a).fv)) :
    M.fv ⊆ (codingClass outer n M a).fv :=
  by
  have hpredicate := parameter_subset_predicate n M a ha
  have houterParameter : outer ∉ M.fv := fun hu =>
    houter (Finset.mem_union_right _ (hpredicate hu))
  rw [codingClass, fv_class_cab, fv_wff_classEq, fv_class_cab]
  exact
    subset_erase_of_subset_of_not_mem
      (fun u hu =>
        Finset.mem_union_left _ ((subset_erase_of_subset_of_not_mem hpredicate hn) hu))
      houterParameter

theorem outerVariablesFresh (n : Var) (M : Class) (a : Var) :
    TEnvFresh [(alpha_dummy_002 M, alpha_dummy_003 n M a)] M.fv :=
  by
  have hsubset :
    M.fv ⊆
      (Wff.classEq M syn_c0).fv ∪ syn_c0.fv ∪
        (syn_cio (alpha_dummy_001 M)
            (finitePredicate (alpha_dummy_001 M) M (alpha_dummy_000 M))).fv :=
    by
    rw [fv_wff_classEq]
    exact fun u hu =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hsubset' :
    M.fv ⊆
      (Wff.classEq M syn_c0).fv ∪ syn_c0.fv ∪ (syn_cio n (finitePredicate n M a)).fv :=
    by
    rw [fv_wff_classEq]
    exact fun u hu =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  exact
    TEnvFresh.cons (fun hu => fresh_025 M (hsubset hu))
      (fun hu => fresh_026 n M a (hsubset' hu)) (by simp [TEnvFresh])

theorem allVariablesFresh (n : Var) (M : Class) (a : Var) (ha : a ∉ M.fv)
    (hn : n ∉ M.fv) :
    TEnvFresh
      [(alpha_dummy_000 M, a), (alpha_dummy_001 M, n),
        (alpha_dummy_008 M, alpha_dummy_009 n M a),
        (alpha_dummy_011 M, alpha_dummy_013 n M a),
        (alpha_dummy_010 M, alpha_dummy_012 n M a),
        (alpha_dummy_002 M, alpha_dummy_003 n M a)]
      M.fv :=
  by
  have hleft :=
    parameter_subset_predicate (alpha_dummy_001 M) M (alpha_dummy_000 M) (fresh_039 M)
  have hright := parameter_subset_predicate n M a ha
  have hleftCode :=
    parameter_subset_codingClass (alpha_dummy_008 M) (alpha_dummy_001 M) M
      (alpha_dummy_000 M) (fresh_039 M) (fresh_040 M) (fresh_042 M)
  have hrightCode :=
    parameter_subset_codingClass (alpha_dummy_009 n M a) n M a ha hn (fresh_043 n M a)
  exact
    TEnvFresh.cons (fresh_039 M) ha
      (TEnvFresh.cons (fresh_040 M) hn
        (TEnvFresh.cons (fun hu => fresh_042 M (Finset.mem_union_right _ (hleft hu)))
          (fun hu => fresh_043 n M a (Finset.mem_union_right _ (hright hu)))
          (TEnvFresh.cons (fun hu => fresh_004 M (hleftCode hu))
            (fun hu => fresh_007 n M a (hrightCode hu))
            (TEnvFresh.cons (fun hu => fresh_003 M (hleftCode hu))
              (fun hu => fresh_006 n M a (hrightCode hu)) (outerVariablesFresh n M a)))))

end FiniteTypeAlpha

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
