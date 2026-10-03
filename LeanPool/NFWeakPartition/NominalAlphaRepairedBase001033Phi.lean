/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001033Phi. -/


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
noncomputable def nominal_df_phi (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cphi A) (.cab y (syn_wrex x A (.classEq (.cv y)
              (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c))
                (.cv x)))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv) 1)
  let alpha_dummy_002 : Var :=
    (freshVar (((Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_000) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar (((Wff.classMem (Class.cv x) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv x) (syn_c1c))).fv ∪ ((Class.cv x)).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_006 : Var :=
    (freshVar (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_007 : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_009 : Var := (freshVar (((Class.cv x)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_010 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_011 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_012 : Var := (freshVar (((Class.cv alpha_dummy_011)).fv) 0)
  let alpha_dummy_013 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv) 0)
  let alpha_dummy_014 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv) 0)
  let alpha_dummy_015 : Var :=
    (freshVar (((Class.cv alpha_dummy_005)).fv ∪ ((Class.cv alpha_dummy_006)).fv) 0)
  let alpha_dummy_016 : Var :=
    (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((Class.cv alpha_dummy_009)).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪
        ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_018 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_019 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_005))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_006))).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_008))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_009))).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((Class.cv alpha_dummy_005)).fv ∪ ((Class.cv alpha_dummy_005)).fv) 0)
  let alpha_dummy_023 : Var :=
    (freshVar (((Class.cv alpha_dummy_008)).fv ∪ ((Class.cv alpha_dummy_008)).fv) 0)
  let alpha_dummy_024 : Var :=
    (freshVar (((Class.cv alpha_dummy_006)).fv ∪ ((Class.cv alpha_dummy_006)).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((Class.cv alpha_dummy_009)).fv ∪ ((Class.cv alpha_dummy_009)).fv) 0)
  let alpha_dummy_026 : Var :=
    (freshVar (((Class.cab alpha_dummy_010
          (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_010))
            (syn_wral alpha_dummy_011 (Class.cv alpha_dummy_010)
              (Wff.classMem (syn_cplc (Class.cv alpha_dummy_011) (syn_c1c))
                (Class.cv alpha_dummy_010)))))).fv) 0)
  let alpha_dummy_027 : Var :=
    (freshVar (((Class.cab alpha_dummy_010
          (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_010))
            (syn_wral alpha_dummy_011 (Class.cv alpha_dummy_010)
              (Wff.classMem (syn_cplc (Class.cv alpha_dummy_011) (syn_c1c))
                (Class.cv alpha_dummy_010)))))).fv) 1)
  let alpha_dummy_028 : Var := (freshVar (((syn_c0)).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_031 : Var :=
    (freshVar (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_032 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv) 0)
  let alpha_dummy_033 : Var :=
    (freshVar (((Class.cv alpha_dummy_030)).fv ∪ ((Class.cv alpha_dummy_031)).fv) 0)
  let alpha_dummy_034 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_030))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_031))).fv) 0)
  let alpha_dummy_035 : Var :=
    (freshVar (((Class.cv alpha_dummy_030)).fv ∪ ((Class.cv alpha_dummy_030)).fv) 0)
  let alpha_dummy_036 : Var :=
    (freshVar (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_031)).fv) 0)
  have fresh_043 : alpha_dummy_000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_044 : alpha_dummy_001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  have support_part_0000 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alpha_dummy_000 ∈
      (((Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_000) (syn_c1c))).fv ∪
        ((Class.cv alpha_dummy_000)).fv) :=
    by
    exact
      (Finset.mem_union_right (((Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv alpha_dummy_000) (syn_c1c))).fv) support_part_0000)
  have support_part_0001 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 :
    x ∈
      (((Wff.classMem (Class.cv x) (syn_cnnc))).fv ∪ ((syn_cplc (Class.cv x) (syn_c1c))).fv ∪
        ((Class.cv x)).fv) :=
    by
    exact
      (Finset.mem_union_right (((Wff.classMem (Class.cv x) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv x) (syn_c1c))).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 :
    alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0002)
  have support_part_0003 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 : x ∈ (((Class.cv x)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0003)
  have support_part_0004 : alpha_dummy_011 ∈ (((Class.cv alpha_dummy_011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0004 : alpha_dummy_011 ∈ (((Class.cv alpha_dummy_011)).fv) := by
    exact support_part_0004
  have support_part_0005 :
    alpha_dummy_005 ∈
      (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0005 :
    alpha_dummy_005 ∈
      (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv)
        support_part_0005)
  have support_part_0006 :
    alpha_dummy_008 ∈
      (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0006 :
    alpha_dummy_008 ∈
      (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv)
        support_part_0006)
  have support_part_0007 : alpha_dummy_005 ∈ (((Class.cv alpha_dummy_005)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alpha_dummy_005 ∈
      (((Class.cv alpha_dummy_005)).fv ∪ ((Class.cv alpha_dummy_006)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_006)).fv) support_part_0007)
  have support_part_0008 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0008 :
    alpha_dummy_008 ∈
      (((Class.cv alpha_dummy_008)).fv ∪ ((Class.cv alpha_dummy_009)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_009)).fv) support_part_0008)
  have support_part_0009 :
    alpha_dummy_006 ∈
      (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0009 :
    alpha_dummy_006 ∈
      (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))).fv)
        support_part_0009)
  have support_part_0010 :
    alpha_dummy_009 ∈
      (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0010 :
    alpha_dummy_009 ∈
      (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))).fv)
        support_part_0010)
  have support_part_0011 : alpha_dummy_006 ∈ (((Class.cv alpha_dummy_006)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0011 :
    alpha_dummy_006 ∈
      (((Class.cv alpha_dummy_005)).fv ∪ ((Class.cv alpha_dummy_006)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_005)).fv) support_part_0011)
  have support_part_0012 : alpha_dummy_009 ∈ (((Class.cv alpha_dummy_009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0012 :
    alpha_dummy_009 ∈
      (((Class.cv alpha_dummy_008)).fv ∪ ((Class.cv alpha_dummy_009)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_008)).fv) support_part_0012)
  have support_part_0013 :
    alpha_dummy_005 ∈ (((syn_ccompl (Class.cv alpha_dummy_005))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0013 :
    alpha_dummy_005 ∈
      (((syn_ccompl (Class.cv alpha_dummy_005))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_006))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_006))).fv) support_part_0013)
  have support_part_0014 :
    alpha_dummy_008 ∈ (((syn_ccompl (Class.cv alpha_dummy_008))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0014 :
    alpha_dummy_008 ∈
      (((syn_ccompl (Class.cv alpha_dummy_008))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_009))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_009))).fv) support_part_0014)
  have support_part_0015 : alpha_dummy_005 ∈ (((Class.cv alpha_dummy_005)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0015 :
    alpha_dummy_005 ∈
      (((Class.cv alpha_dummy_005)).fv ∪ ((Class.cv alpha_dummy_005)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_005)).fv) support_part_0015)
  have support_part_0016 : alpha_dummy_008 ∈ (((Class.cv alpha_dummy_008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0016 :
    alpha_dummy_008 ∈
      (((Class.cv alpha_dummy_008)).fv ∪ ((Class.cv alpha_dummy_008)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_008)).fv) support_part_0016)
  have support_part_0017 :
    alpha_dummy_006 ∈ (((syn_ccompl (Class.cv alpha_dummy_006))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0017 :
    alpha_dummy_006 ∈
      (((syn_ccompl (Class.cv alpha_dummy_005))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_006))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_005))).fv) support_part_0017)
  have support_part_0018 :
    alpha_dummy_009 ∈ (((syn_ccompl (Class.cv alpha_dummy_009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0018 :
    alpha_dummy_009 ∈
      (((syn_ccompl (Class.cv alpha_dummy_008))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_009))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_008))).fv) support_part_0018)
  have support_part_0019 : alpha_dummy_006 ∈ (((Class.cv alpha_dummy_006)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0019 :
    alpha_dummy_006 ∈
      (((Class.cv alpha_dummy_006)).fv ∪ ((Class.cv alpha_dummy_006)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_006)).fv) support_part_0019)
  have support_part_0020 : alpha_dummy_009 ∈ (((Class.cv alpha_dummy_009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0020 :
    alpha_dummy_009 ∈
      (((Class.cv alpha_dummy_009)).fv ∪ ((Class.cv alpha_dummy_009)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_009)).fv) support_part_0020)
  have support_part_0021 : alpha_dummy_011 ∈ (((Class.cv alpha_dummy_011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0021 :
    alpha_dummy_011 ∈ (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0021)
  have support_part_0022 :
    alpha_dummy_030 ∈
      (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0022 :
    alpha_dummy_030 ∈
      (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv)
        support_part_0022)
  have support_part_0023 : alpha_dummy_030 ∈ (((Class.cv alpha_dummy_030)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0023 :
    alpha_dummy_030 ∈
      (((Class.cv alpha_dummy_030)).fv ∪ ((Class.cv alpha_dummy_031)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_031)).fv) support_part_0023)
  have support_part_0024 :
    alpha_dummy_031 ∈
      (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0024 :
    alpha_dummy_031 ∈
      (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))).fv)
        support_part_0024)
  have support_part_0025 : alpha_dummy_031 ∈ (((Class.cv alpha_dummy_031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0025 :
    alpha_dummy_031 ∈
      (((Class.cv alpha_dummy_030)).fv ∪ ((Class.cv alpha_dummy_031)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_030)).fv) support_part_0025)
  have support_part_0026 :
    alpha_dummy_030 ∈ (((syn_ccompl (Class.cv alpha_dummy_030))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0026 :
    alpha_dummy_030 ∈
      (((syn_ccompl (Class.cv alpha_dummy_030))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_031))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_031))).fv) support_part_0026)
  have support_part_0027 : alpha_dummy_030 ∈ (((Class.cv alpha_dummy_030)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 :
    alpha_dummy_030 ∈
      (((Class.cv alpha_dummy_030)).fv ∪ ((Class.cv alpha_dummy_030)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_030)).fv) support_part_0027)
  have support_part_0028 :
    alpha_dummy_031 ∈ (((syn_ccompl (Class.cv alpha_dummy_031))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0028 :
    alpha_dummy_031 ∈
      (((syn_ccompl (Class.cv alpha_dummy_030))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_031))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_030))).fv) support_part_0028)
  have support_part_0029 : alpha_dummy_031 ∈ (((Class.cv alpha_dummy_031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0029 :
    alpha_dummy_031 ∈
      (((Class.cv alpha_dummy_031)).fv ∪ ((Class.cv alpha_dummy_031)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_031)).fv) support_part_0029)
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_006, alpha_dummy_009), (alpha_dummy_005, alpha_dummy_008),
        (alpha_dummy_004, alpha_dummy_007), (alpha_dummy_002, alpha_dummy_003),
        (alpha_dummy_000, x), (alpha_dummy_001, y)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_004)
            (syn_cun (Class.cv alpha_dummy_005) (Class.cv alpha_dummy_006)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_007)
            (syn_cun (Class.cv alpha_dummy_008) (Class.cv alpha_dummy_009))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
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
              (freshVar_injective (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv) (by decide))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_000)).fv ∪ ((syn_c1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv x)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have split_alpha_0001 :
    TAlphaWff
      [(alpha_dummy_031, alpha_dummy_031), (alpha_dummy_030, alpha_dummy_030),
        (alpha_dummy_029, alpha_dummy_029), (alpha_dummy_011, alpha_dummy_011),
        (alpha_dummy_010, alpha_dummy_010), (alpha_dummy_027, alpha_dummy_027),
        (alpha_dummy_026, alpha_dummy_026), (alpha_dummy_002, alpha_dummy_003),
        (alpha_dummy_000, x), (alpha_dummy_001, y)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_029)
            (syn_cun (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_029)
            (syn_cun (Class.cv alpha_dummy_030) (Class.cv alpha_dummy_031))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
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
              (freshVar_injective (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alpha_dummy_011)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_002, alpha_dummy_003), (alpha_dummy_000, x), (alpha_dummy_001, y)]
      (Wff.classMem (Class.cv alpha_dummy_000) (syn_cnnc))
      (Wff.classMem (Class.cv x) (syn_cnnc)) :=
    (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))
      (TAlphaClass.cab (TAlphaWff.all (TAlphaWff.imp
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
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                      (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg split_alpha_0001)))))) (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alpha_dummy_010
                      (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_010))
                        (syn_wral alpha_dummy_011 (Class.cv alpha_dummy_010)
                          (Wff.classMem (syn_cplc (Class.cv alpha_dummy_011) (syn_c1c))
                            (Class.cv alpha_dummy_010)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab alpha_dummy_010
                      (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_010))
                        (syn_wral alpha_dummy_011 (Class.cv alpha_dummy_010)
                          (Wff.classMem (syn_cplc (Class.cv alpha_dummy_011) (syn_c1c))
                            (Class.cv alpha_dummy_010)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_fv_fresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                  (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg split_alpha_0000))))))) split_alpha_0002))
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg split_alpha_0002))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
