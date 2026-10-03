/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001032Spfin. -/


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
noncomputable def nominal_df_spfin (x : Var) (z : Var) (a : Var) (dv_a_x : a ≠ x)
    (dv_a_z : a ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cspfin) (syn_cint (.cab a
            (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
                (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alpha_dummy_003 : Var :=
    (freshVar (((Class.cab alpha_dummy_000
          (syn_wa (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv alpha_dummy_000))
            (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.all alpha_dummy_002
                (Wff.imp (syn_wsfin (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))
                  (Wff.objMem alpha_dummy_002 alpha_dummy_000))))))).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((Class.cab alpha_dummy_000
          (syn_wa (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv alpha_dummy_000))
            (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.all alpha_dummy_002
                (Wff.imp (syn_wsfin (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))
                  (Wff.objMem alpha_dummy_002 alpha_dummy_000))))))).fv) 1)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cab a (syn_wa (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv a))
            (syn_wral x (Class.cv a) (Wff.all z
                (Wff.imp (syn_wsfin (Class.cv z) (Class.cv x)) (Wff.objMem z a))))))).fv) 0)
  let alpha_dummy_006 : Var :=
    (freshVar (((Class.cab a (syn_wa (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv a))
            (syn_wral x (Class.cv a) (Wff.all z
                (Wff.imp (syn_wsfin (Class.cv z) (Class.cv x)) (Wff.objMem z a))))))).fv) 1)
  let alpha_dummy_007 : Var := (freshVar (((syn_cvv)).fv) 0)
  let alpha_dummy_008 : Var :=
    (freshVar (({ alpha_dummy_007 } : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
            (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007)))).fv) 0)
  let alpha_dummy_009 : Var :=
    (freshVar (((Class.cab alpha_dummy_008 (Wff.classEq (Class.cab alpha_dummy_007
              (syn_wa (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
                (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007))))
            (syn_csn (Class.cv alpha_dummy_008))))).fv) 0)
  let alpha_dummy_010 : Var :=
    (freshVar (((Class.cab alpha_dummy_008 (Wff.classEq (Class.cab alpha_dummy_007
              (syn_wa (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
                (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007))))
            (syn_csn (Class.cv alpha_dummy_008))))).fv) 1)
  let alpha_dummy_011 : Var :=
    (freshVar (((Class.cab alpha_dummy_000
          (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
            (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
              (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                (Class.cv alpha_dummy_000)))))).fv) 0)
  let alpha_dummy_012 : Var :=
    (freshVar (((Class.cab alpha_dummy_000
          (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
            (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
              (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                (Class.cv alpha_dummy_000)))))).fv) 1)
  let alpha_dummy_013 : Var := (freshVar (((syn_c0)).fv) 0)
  let alpha_dummy_014 : Var :=
    (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪
        ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_018 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_019 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_020 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_019)).fv) 0)
  let alpha_dummy_023 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_018))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_019))).fv) 0)
  let alpha_dummy_024 : Var :=
    (freshVar (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_018)).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_019)).fv) 0)
  let alpha_dummy_026 : Var := (freshVar (((Class.cv alpha_dummy_008)).fv) 0)
  let alpha_dummy_027 : Var :=
    (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_028 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv x)).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))).fv) 0)
  let alpha_dummy_031 : Var :=
    (freshVar (((syn_cpw (Class.cv alpha_dummy_027))).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_032 : Var :=
    (freshVar (((syn_cpw (Class.cv alpha_dummy_028))).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_033 : Var := (freshVar (((Class.cv alpha_dummy_027)).fv) 0)
  let alpha_dummy_034 : Var := (freshVar (((Class.cv alpha_dummy_028)).fv) 0)
  let alpha_dummy_035 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv) 0)
  let alpha_dummy_036 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv) 0)
  let alpha_dummy_037 : Var :=
    (freshVar (((Class.cv alpha_dummy_033)).fv ∪ ((Class.cv alpha_dummy_027)).fv) 0)
  let alpha_dummy_038 : Var :=
    (freshVar (((Class.cv alpha_dummy_034)).fv ∪ ((Class.cv alpha_dummy_028)).fv) 0)
  have support_part_0000 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0000)
  have support_part_0001 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0001
  have support_part_0002 :
    alpha_dummy_018 ∈
      (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0002 :
    alpha_dummy_018 ∈
      (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv)
        support_part_0002)
  have support_part_0003 : alpha_dummy_018 ∈ (((Class.cv alpha_dummy_018)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 :
    alpha_dummy_018 ∈
      (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_019)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_019)).fv) support_part_0003)
  have support_part_0004 :
    alpha_dummy_019 ∈
      (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alpha_dummy_019 ∈
      (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))).fv)
        support_part_0004)
  have support_part_0005 : alpha_dummy_019 ∈ (((Class.cv alpha_dummy_019)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alpha_dummy_019 ∈
      (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_019)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_018)).fv) support_part_0005)
  have support_part_0006 :
    alpha_dummy_018 ∈ (((syn_ccompl (Class.cv alpha_dummy_018))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0006 :
    alpha_dummy_018 ∈
      (((syn_ccompl (Class.cv alpha_dummy_018))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_019))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_019))).fv) support_part_0006)
  have support_part_0007 : alpha_dummy_018 ∈ (((Class.cv alpha_dummy_018)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alpha_dummy_018 ∈
      (((Class.cv alpha_dummy_018)).fv ∪ ((Class.cv alpha_dummy_018)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_018)).fv) support_part_0007)
  have support_part_0008 :
    alpha_dummy_019 ∈ (((syn_ccompl (Class.cv alpha_dummy_019))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alpha_dummy_019 ∈
      (((syn_ccompl (Class.cv alpha_dummy_018))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_019))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_018))).fv) support_part_0008)
  have support_part_0009 : alpha_dummy_019 ∈ (((Class.cv alpha_dummy_019)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alpha_dummy_019 ∈
      (((Class.cv alpha_dummy_019)).fv ∪ ((Class.cv alpha_dummy_019)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_019)).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    exact support_part_0010
  have support_part_0011 :
    alpha_dummy_033 ∈
      (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0011 :
    alpha_dummy_033 ∈
      (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv)
        support_part_0011)
  have support_part_0012 :
    alpha_dummy_034 ∈
      (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0012 :
    alpha_dummy_034 ∈
      (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv)
        support_part_0012)
  have support_part_0013 : alpha_dummy_033 ∈ (((Class.cv alpha_dummy_033)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0013 :
    alpha_dummy_033 ∈
      (((Class.cv alpha_dummy_033)).fv ∪ ((Class.cv alpha_dummy_027)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_027)).fv) support_part_0013)
  have support_part_0014 : alpha_dummy_034 ∈ (((Class.cv alpha_dummy_034)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alpha_dummy_034 ∈
      (((Class.cv alpha_dummy_034)).fv ∪ ((Class.cv alpha_dummy_028)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_028)).fv) support_part_0014)
  have support_part_0015 :
    alpha_dummy_027 ∈ (((syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c,
      fv_syn_cnin, fv_syn_cpw, eq_self, true_or]
  have support_mem_0015 :
    alpha_dummy_027 ∈
      (((syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))).fv)
        support_part_0015)
  have support_part_0016 :
    alpha_dummy_028 ∈ (((syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c,
      fv_syn_cnin, fv_syn_cpw, eq_self, true_or]
  have support_mem_0016 :
    alpha_dummy_028 ∈
      (((syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))).fv)
        support_part_0016)
  have support_part_0017 :
    alpha_dummy_027 ∈ (((syn_cpw (Class.cv alpha_dummy_027))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]
  have support_mem_0017 :
    alpha_dummy_027 ∈ (((syn_cpw (Class.cv alpha_dummy_027))).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0017)
  have support_part_0018 :
    alpha_dummy_028 ∈ (((syn_cpw (Class.cv alpha_dummy_028))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]
  have support_mem_0018 :
    alpha_dummy_028 ∈ (((syn_cpw (Class.cv alpha_dummy_028))).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0018)
  have support_part_0019 : alpha_dummy_027 ∈ (((Class.cv alpha_dummy_027)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0019 : alpha_dummy_027 ∈ (((Class.cv alpha_dummy_027)).fv) := by
    exact support_part_0019
  have support_part_0020 : alpha_dummy_028 ∈ (((Class.cv alpha_dummy_028)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0020 : alpha_dummy_028 ∈ (((Class.cv alpha_dummy_028)).fv) := by
    exact support_part_0020
  have support_part_0021 :
    alpha_dummy_027 ∈
      (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0021 :
    alpha_dummy_027 ∈
      (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_033) (Class.cv alpha_dummy_027))).fv)
        support_part_0021)
  have support_part_0022 :
    alpha_dummy_028 ∈
      (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0022 :
    alpha_dummy_028 ∈
      (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_034) (Class.cv alpha_dummy_028))).fv)
        support_part_0022)
  have support_part_0023 : alpha_dummy_027 ∈ (((Class.cv alpha_dummy_027)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0023 :
    alpha_dummy_027 ∈
      (((Class.cv alpha_dummy_033)).fv ∪ ((Class.cv alpha_dummy_027)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_033)).fv) support_part_0023)
  have support_part_0024 : alpha_dummy_028 ∈ (((Class.cv alpha_dummy_028)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0024 :
    alpha_dummy_028 ∈
      (((Class.cv alpha_dummy_034)).fv ∪ ((Class.cv alpha_dummy_028)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_034)).fv) support_part_0024)
  have support_part_0025 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0025 :
    alpha_dummy_002 ∈
      (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_001)).fv) support_part_0025)
  have support_part_0026 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : z ∈ (((Class.cv z)).fv ∪ ((Class.cv x)).fv) := by
    exact (Finset.mem_union_left (((Class.cv x)).fv) support_part_0026)
  have support_part_0027 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_002)).fv) support_part_0027)
  have support_part_0028 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0028 : x ∈ (((Class.cv z)).fv ∪ ((Class.cv x)).fv) := by
    exact (Finset.mem_union_right (((Class.cv z)).fv) support_part_0028)
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_019, alpha_dummy_019), (alpha_dummy_018, alpha_dummy_018),
        (alpha_dummy_017, alpha_dummy_017), (alpha_dummy_001, alpha_dummy_001),
        (alpha_dummy_000, alpha_dummy_000), (alpha_dummy_012, alpha_dummy_012),
        (alpha_dummy_011, alpha_dummy_011), (alpha_dummy_007, alpha_dummy_007),
        (alpha_dummy_008, alpha_dummy_008), (alpha_dummy_010, alpha_dummy_010),
        (alpha_dummy_009, alpha_dummy_009), (alpha_dummy_000, a),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_017)
            (syn_cun (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_017)
            (syn_cun (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have split_alpha_0001 :
    TAlphaWff
      [(alpha_dummy_007, alpha_dummy_007), (alpha_dummy_008, alpha_dummy_008),
        (alpha_dummy_010, alpha_dummy_010), (alpha_dummy_009, alpha_dummy_009),
        (alpha_dummy_000, a), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
        (Wff.neg (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
        (Wff.neg (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007)))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.all (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq
        (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq
        (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.all (TAlphaWff.imp
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                    (TAlphaWff.neg split_alpha_0000)))))) (TAlphaClass.cv
                            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                  (freshVar_injective (((Class.cab alpha_dummy_000
                        (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                          (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                            (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                              (Class.cv alpha_dummy_000)))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alpha_dummy_000
                        (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                          (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                            (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                              (Class.cv alpha_dummy_000)))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cab
            (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))
          (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_019, alpha_dummy_019), (alpha_dummy_018, alpha_dummy_018),
        (alpha_dummy_017, alpha_dummy_017), (alpha_dummy_001, alpha_dummy_001),
        (alpha_dummy_000, alpha_dummy_000), (alpha_dummy_012, alpha_dummy_012),
        (alpha_dummy_011, alpha_dummy_011), (alpha_dummy_002, z), (alpha_dummy_001, x),
        (alpha_dummy_000, a), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_017)
            (syn_cun (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_017)
            (syn_cun (Class.cv alpha_dummy_018) (Class.cv alpha_dummy_019))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                            (TAlphaVar.here _ _ _))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.objEq (TAlphaVar.here _ _ _)
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
              (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have split_alpha_0003 :
    TAlphaWff
      [(alpha_dummy_002, z), (alpha_dummy_001, x), (alpha_dummy_000, a),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.classMem (Class.cv alpha_dummy_001) (syn_cnnc))
      (Wff.classMem (Class.cv x) (syn_cnnc)) :=
    (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.all (TAlphaWff.imp
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                          (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg split_alpha_0002)))))) (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alpha_dummy_000
                      (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                        (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                          (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                            (Class.cv alpha_dummy_000)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab alpha_dummy_000
                      (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                        (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                          (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                            (Class.cv alpha_dummy_000)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))))))
  have split_alpha_0004 :
    TAlphaWff
      [(alpha_dummy_002, z), (alpha_dummy_001, x), (alpha_dummy_000, a),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.neg (Wff.imp (Wff.classMem (Class.cv alpha_dummy_002) (syn_cnnc))
          (Wff.neg (Wff.classMem (Class.cv alpha_dummy_001) (syn_cnnc)))))
      (Wff.neg (Wff.imp (Wff.classMem (Class.cv z) (syn_cnnc))
          (Wff.neg (Wff.classMem (Class.cv x) (syn_cnnc))))) :=
    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.all (TAlphaWff.imp
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq
        (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.objEq
        (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _)))))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.all (TAlphaWff.imp
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                    (TAlphaWff.neg split_alpha_0002)))))) (TAlphaClass.cv
                            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                  (freshVar_injective (((Class.cab alpha_dummy_000
                        (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                          (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                            (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                              (Class.cv alpha_dummy_000)))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alpha_dummy_000
                        (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                          (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                            (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                              (Class.cv alpha_dummy_000)))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) split_alpha_0003)
  have split_alpha_0005 :
    TAlphaWff
      [(alpha_dummy_029, alpha_dummy_030), (alpha_dummy_027, alpha_dummy_028),
        (alpha_dummy_002, z), (alpha_dummy_001, x), (alpha_dummy_000, a),
        (alpha_dummy_004, alpha_dummy_006), (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_029)
          (syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_029)
            (syn_cnin (syn_cpw (Class.cv alpha_dummy_027)) (syn_c1c)))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_030)
          (syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_030)
            (syn_cnin (syn_cpw (Class.cv alpha_dummy_028)) (syn_c1c))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _)))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (TAlphaVar.here _ _ _)))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have split_alpha_0006 :
    TAlphaWff
      [(alpha_dummy_000, a), (alpha_dummy_004, alpha_dummy_006),
        (alpha_dummy_003, alpha_dummy_005)]
      (Wff.imp (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv alpha_dummy_000)) (Wff.neg
          (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000) (Wff.all alpha_dummy_002
              (Wff.imp (syn_wsfin (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))
                (Wff.objMem alpha_dummy_002 alpha_dummy_000))))))
      (Wff.imp (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv a)) (Wff.neg
          (syn_wral x (Class.cv a) (Wff.all z
              (Wff.imp (syn_wsfin (Class.cv z) (Class.cv x)) (Wff.objMem z a)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                    (((Class.cab alpha_dummy_008 (Wff.classEq (Class.cab alpha_dummy_007
                            (syn_wa (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
                              (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007))))
                          (syn_csn (Class.cv alpha_dummy_008))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alpha_dummy_008 (Wff.classEq
                          (Class.cab alpha_dummy_007
                            (syn_wa (Wff.classMem (Class.cv alpha_dummy_007) (syn_cnnc))
                              (Wff.classMem (syn_cvv) (Class.cv alpha_dummy_007))))
                          (syn_csn (Class.cv alpha_dummy_008))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg split_alpha_0001))
                    (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                            (TAlphaVar.here _ _ _)))))))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  dv_a_x (TAlphaVar.here _ _ _)))) (TAlphaWff.all (TAlphaWff.imp
                (TAlphaWff.conj split_alpha_0004 (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg split_alpha_0005)))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020
        0)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0024 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020
        0)) (TAlphaVar.here _ _ _))))))))))))) (TAlphaClass.cv (TAlphaVar.here _ _ _))))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0)) (TAlphaVar.there
                              (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                              (TAlphaVar.here _ _ _))))))))
                (TAlphaWff.objMem (TAlphaVar.here _ _ _)
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_a_z
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      dv_a_x (TAlphaVar.here _ _ _))))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.neg split_alpha_0006))) (TAlphaWff.objMem
              (TAlphaVar.there (freshVar_injective (((Class.cab alpha_dummy_000 (syn_wa
                        (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv alpha_dummy_000))
                        (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                          (Wff.all alpha_dummy_002 (Wff.imp
                              (syn_wsfin (Class.cv alpha_dummy_002) (Class.cv alpha_dummy_001))
                              (Wff.objMem alpha_dummy_002 alpha_dummy_000))))))).fv)
                  (by decide)) (freshVar_injective (((Class.cab a
                      (syn_wa (Wff.classMem (syn_cncfin (syn_cvv)) (Class.cv a))
                        (syn_wral x (Class.cv a) (Wff.all z
                            (Wff.imp (syn_wsfin (Class.cv z) (Class.cv x))
                              (Wff.objMem z a))))))).fv) (by decide)) (TAlphaVar.here _ _ _))
              (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
