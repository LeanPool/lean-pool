/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001018P6. -/


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
noncomputable def nominal_df_p6 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.classEq (syn_cp6 A)
        (.cab x (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) A))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var :=
    (freshVar (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))
            A)).fv ∪
        ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv)
      0)
  let alpha_dummy_002 : Var :=
    (freshVar (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv ∪
        ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar
      (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ (A).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x))))).fv ∪ (A).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) 0)
  let alpha_dummy_006 : Var :=
    (freshVar (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) 1)
  let alpha_dummy_007 : Var :=
    (freshVar (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) 2)
  let alpha_dummy_008 : Var :=
    (freshVar (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 0)
  let alpha_dummy_009 : Var :=
    (freshVar (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 1)
  let alpha_dummy_010 : Var :=
    (freshVar (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) 2)
  let alpha_dummy_011 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_006))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))))).fv) 0)
  let alpha_dummy_012 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_009))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))))).fv) 0)
  let alpha_dummy_013 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_006)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_006)))).fv) 0)
  let alpha_dummy_014 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_009)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_009)))).fv) 0)
  let alpha_dummy_015 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_006))).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_009))).fv) 0)
  let alpha_dummy_017 : Var := (freshVar (((Class.cv alpha_dummy_006)).fv) 0)
  let alpha_dummy_018 : Var := (freshVar (((Class.cv alpha_dummy_009)).fv) 0)
  let alpha_dummy_019 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))).fv) 0)
  let alpha_dummy_023 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_007)))).fv) 0)
  let alpha_dummy_024 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_006))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_006))).fv) 0)
  let alpha_dummy_026 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_009))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_009))).fv) 0)
  let alpha_dummy_027 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_007))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_007))).fv) 0)
  let alpha_dummy_028 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_010))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_010))).fv) 0)
  let alpha_dummy_029 : Var := (freshVar (((Class.cv alpha_dummy_007)).fv) 0)
  let alpha_dummy_030 : Var := (freshVar (((Class.cv alpha_dummy_010)).fv) 0)
  let alpha_dummy_031 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_032 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_033 : Var := (freshVar (((syn_csn (Class.cv x))).fv) 0)
  let alpha_dummy_034 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_035 : Var := (freshVar (((Class.cv x)).fv) 0)
  have fresh_010 :
    alpha_dummy_001 ∉
      (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv ∪
        ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))
            A)).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv ∪
          ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv)
        0
  have fresh_011 :
    alpha_dummy_002 ∉
      (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv ∪
        ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv ∪
          ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv)
        0
  have fresh_038 :
    alpha_dummy_003 ∉
      (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ (A).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ (A).fv)
        0
  have fresh_039 :
    alpha_dummy_004 ∉
      (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x))))).fv ∪ (A).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x))))).fv ∪ (A).fv) 0
  have fresh_040 : alpha_dummy_000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have support_part_0000 :
    alpha_dummy_006 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_006))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alpha_dummy_006 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))))).fv)
        support_part_0000)
  have support_part_0001 :
    alpha_dummy_009 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_009))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0001 :
    alpha_dummy_009 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_009))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))))).fv)
        support_part_0001)
  have support_part_0002 :
    alpha_dummy_006 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_006)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alpha_dummy_006 ∈
      (((syn_csn (syn_csn (Class.cv alpha_dummy_006)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_006)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_006)))).fv)
        support_part_0002)
  have support_part_0003 :
    alpha_dummy_009 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_009)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    alpha_dummy_009 ∈
      (((syn_csn (syn_csn (Class.cv alpha_dummy_009)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_009)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_009)))).fv)
        support_part_0003)
  have support_part_0004 :
    alpha_dummy_006 ∈ (((syn_csn (Class.cv alpha_dummy_006))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alpha_dummy_006 ∈ (((syn_csn (Class.cv alpha_dummy_006))).fv) :=
    by exact support_part_0004
  have support_part_0005 :
    alpha_dummy_009 ∈ (((syn_csn (Class.cv alpha_dummy_009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : alpha_dummy_009 ∈ (((syn_csn (Class.cv alpha_dummy_009))).fv) :=
    by exact support_part_0005
  have support_part_0006 : alpha_dummy_006 ∈ (((Class.cv alpha_dummy_006)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alpha_dummy_006 ∈ (((Class.cv alpha_dummy_006)).fv) := by
    exact support_part_0006
  have support_part_0007 : alpha_dummy_009 ∈ (((Class.cv alpha_dummy_009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : alpha_dummy_009 ∈ (((Class.cv alpha_dummy_009)).fv) := by
    exact support_part_0007
  have support_part_0008 :
    alpha_dummy_006 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alpha_dummy_006 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv)
        support_part_0008)
  have support_part_0009 :
    alpha_dummy_009 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0009 :
    alpha_dummy_009 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv)
        support_part_0009)
  have support_part_0010 :
    alpha_dummy_006 ∈
      (((syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alpha_dummy_006 ∈
      (((syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))).fv) :=
    by exact support_part_0010
  have support_part_0011 :
    alpha_dummy_009 ∈
      (((syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 :
    alpha_dummy_009 ∈
      (((syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))).fv) :=
    by exact support_part_0011
  have support_part_0012 :
    alpha_dummy_006 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alpha_dummy_006 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_007)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_007)))).fv)
        support_part_0012)
  have support_part_0013 :
    alpha_dummy_009 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0013 :
    alpha_dummy_009 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))).fv)
        support_part_0013)
  have support_part_0014 :
    alpha_dummy_006 ∈ (((syn_csn (Class.cv alpha_dummy_006))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alpha_dummy_006 ∈
      (((syn_csn (Class.cv alpha_dummy_006))).fv ∪ ((syn_csn (Class.cv alpha_dummy_006))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_006))).fv) support_part_0014)
  have support_part_0015 :
    alpha_dummy_009 ∈ (((syn_csn (Class.cv alpha_dummy_009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    alpha_dummy_009 ∈
      (((syn_csn (Class.cv alpha_dummy_009))).fv ∪ ((syn_csn (Class.cv alpha_dummy_009))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_009))).fv) support_part_0015)
  have support_part_0016 :
    alpha_dummy_007 ∈
      (((syn_ccompl (syn_csn
            (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alpha_dummy_007 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_006))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_006))))).fv)
        support_part_0016)
  have support_part_0017 :
    alpha_dummy_010 ∈
      (((syn_ccompl (syn_csn
            (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0017 :
    alpha_dummy_010 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_009))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_009))))).fv)
        support_part_0017)
  have support_part_0018 :
    alpha_dummy_007 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alpha_dummy_007 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007)))).fv)
        support_part_0018)
  have support_part_0019 :
    alpha_dummy_010 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0019 :
    alpha_dummy_010 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010)))).fv)
        support_part_0019)
  have support_part_0020 :
    alpha_dummy_007 ∈
      (((syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alpha_dummy_007 ∈
      (((syn_cpr (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))).fv) :=
    by exact support_part_0020
  have support_part_0021 :
    alpha_dummy_010 ∈
      (((syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 :
    alpha_dummy_010 ∈
      (((syn_cpr (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))).fv) :=
    by exact support_part_0021
  have support_part_0022 :
    alpha_dummy_007 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_007)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alpha_dummy_007 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_007)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))).fv)
        support_part_0022)
  have support_part_0023 :
    alpha_dummy_010 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0023 :
    alpha_dummy_010 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))).fv)
        support_part_0023)
  have support_part_0024 :
    alpha_dummy_007 ∈ (((syn_csn (Class.cv alpha_dummy_007))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alpha_dummy_007 ∈
      (((syn_csn (Class.cv alpha_dummy_007))).fv ∪ ((syn_csn (Class.cv alpha_dummy_007))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_007))).fv) support_part_0024)
  have support_part_0025 :
    alpha_dummy_010 ∈ (((syn_csn (Class.cv alpha_dummy_010))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    alpha_dummy_010 ∈
      (((syn_csn (Class.cv alpha_dummy_010))).fv ∪ ((syn_csn (Class.cv alpha_dummy_010))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_010))).fv) support_part_0025)
  have support_part_0026 : alpha_dummy_007 ∈ (((Class.cv alpha_dummy_007)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alpha_dummy_007 ∈ (((Class.cv alpha_dummy_007)).fv) := by
    exact support_part_0026
  have support_part_0027 : alpha_dummy_010 ∈ (((Class.cv alpha_dummy_010)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : alpha_dummy_010 ∈ (((Class.cv alpha_dummy_010)).fv) := by
    exact support_part_0027
  have support_part_0028 :
    alpha_dummy_000 ∈
      (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin,
      fv_syn_csn, fv_syn_cvv, fv_syn_cxpk, eq_self, true_or, or_true]
  have support_mem_0028 :
    alpha_dummy_000 ∈
      (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv ∪
        ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))
            A)).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000)))) A)).fv)
        support_part_0028)
  have support_part_0029 :
    x ∈ (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin,
      fv_syn_csn, fv_syn_cvv, fv_syn_cxpk, eq_self, true_or, or_true]
  have support_mem_0029 :
    x ∈
      (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv ∪
        ((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x)))) A)).fv)
        support_part_0029)
  have support_part_0030 :
    alpha_dummy_000 ∈
      (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn,
      fv_syn_cvv, fv_syn_cxpk, eq_self, or_true]
  have support_mem_0030 :
    alpha_dummy_000 ∈
      (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ (A).fv) :=
    by exact (Finset.mem_union_left ((A).fv) support_part_0030)
  have support_part_0031 :
    x ∈ (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn,
      fv_syn_cvv, fv_syn_cxpk, eq_self, or_true]
  have support_mem_0031 :
    x ∈ (((syn_cxpk (syn_cvv) (syn_csn (syn_csn (Class.cv x))))).fv ∪ (A).fv) := by
    exact (Finset.mem_union_left ((A).fv) support_part_0031)
  have support_part_0032 :
    alpha_dummy_000 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0032 :
    alpha_dummy_000 ∈
      (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) :=
    by exact (Finset.mem_union_right (((syn_cvv)).fv) support_part_0032)
  have support_part_0033 : x ∈ (((syn_csn (syn_csn (Class.cv x)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0033 : x ∈ (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) :=
    by exact (Finset.mem_union_right (((syn_cvv)).fv) support_part_0033)
  have support_part_0034 :
    alpha_dummy_000 ∈ (((syn_csn (Class.cv alpha_dummy_000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0034 : alpha_dummy_000 ∈ (((syn_csn (Class.cv alpha_dummy_000))).fv) :=
    by exact support_part_0034
  have support_part_0035 : x ∈ (((syn_csn (Class.cv x))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0035 : x ∈ (((syn_csn (Class.cv x))).fv) := by exact support_part_0035
  have support_part_0036 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0036 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    exact support_part_0036
  have support_part_0037 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0037 : x ∈ (((Class.cv x)).fv) := by exact support_part_0037
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_023, alpha_dummy_024), (alpha_dummy_021, alpha_dummy_022),
        (alpha_dummy_019, alpha_dummy_020), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_007, alpha_dummy_010), (alpha_dummy_006, alpha_dummy_009),
        (alpha_dummy_005, alpha_dummy_008), (alpha_dummy_003, alpha_dummy_004),
        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_023)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_023)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_024)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_024)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                  (TAlphaVar.there (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                                      (by decide)) (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv x)))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                  (TAlphaVar.there (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                                      (by decide)) (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv x)))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                    (TAlphaVar.here _ _ _)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                    (TAlphaVar.here _ _ _)))))))))))))))))
  have split_alpha_0001 :
    TAlphaWff
      [(alpha_dummy_007, alpha_dummy_010), (alpha_dummy_006, alpha_dummy_009),
        (alpha_dummy_005, alpha_dummy_008), (alpha_dummy_003, alpha_dummy_004),
        (alpha_dummy_001, alpha_dummy_002), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classEq (Class.cv alpha_dummy_005)
          (syn_copk (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))) (Wff.neg
          (syn_wa (Wff.classMem (Class.cv alpha_dummy_006) (syn_cvv))
            (Wff.classMem (Class.cv alpha_dummy_007)
              (syn_csn (syn_csn (Class.cv alpha_dummy_000)))))))
      (Wff.imp (Wff.classEq (Class.cv alpha_dummy_008)
          (syn_copk (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))) (Wff.neg
          (syn_wa (Wff.classMem (Class.cv alpha_dummy_009) (syn_cvv))
            (Wff.classMem (Class.cv alpha_dummy_010) (syn_csn (syn_csn (Class.cv x))))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
              (by decide))
            (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                (by decide))
              (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective
        (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) (by decide))
        (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
        (by decide)) (TAlphaVar.here _ _ _))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective
        (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) (by decide))
        (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
        (by decide)) (TAlphaVar.here _ _ _))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg split_alpha_0000))))))))))))))
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective
                  (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                  (by decide)) (freshVar_injective
                  (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab
              (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 2))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 2)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                                    (TAlphaVar.here _ _ _)))))))))))))))))
  have split_alpha_0002 :
    TAlphaWff
      [(alpha_dummy_023, alpha_dummy_024), (alpha_dummy_021, alpha_dummy_022),
        (alpha_dummy_019, alpha_dummy_020), (alpha_dummy_011, alpha_dummy_012),
        (alpha_dummy_007, alpha_dummy_010), (alpha_dummy_006, alpha_dummy_009),
        (alpha_dummy_005, alpha_dummy_008), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_023)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_006)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_023)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_007))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_024)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_009)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_024)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_010)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                  (TAlphaVar.there (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                                      (by decide)) (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv x)))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                  (TAlphaVar.there (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                                      (by decide)) (freshVar_injective (((syn_cvv)).fv ∪
                                        ((syn_csn (syn_csn (Class.cv x)))).fv) (by decide))
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                    (TAlphaVar.here _ _ _)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0024 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0025 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0020 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0021 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0019 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                                    (TAlphaVar.here _ _ _)))))))))))))))))
  have split_alpha_0003 :
    TAlphaWff
      [(alpha_dummy_007, alpha_dummy_010), (alpha_dummy_006, alpha_dummy_009),
        (alpha_dummy_005, alpha_dummy_008), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classEq (Class.cv alpha_dummy_005)
          (syn_copk (Class.cv alpha_dummy_006) (Class.cv alpha_dummy_007))) (Wff.neg
          (syn_wa (Wff.classMem (Class.cv alpha_dummy_006) (syn_cvv))
            (Wff.classMem (Class.cv alpha_dummy_007)
              (syn_csn (syn_csn (Class.cv alpha_dummy_000)))))))
      (Wff.imp (Wff.classEq (Class.cv alpha_dummy_008)
          (syn_copk (Class.cv alpha_dummy_009) (Class.cv alpha_dummy_010))) (Wff.neg
          (syn_wa (Wff.classMem (Class.cv alpha_dummy_009) (syn_cvv))
            (Wff.classMem (Class.cv alpha_dummy_010) (syn_csn (syn_csn (Class.cv x))))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
              (by decide))
            (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                (by decide))
              (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective
        (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) (by decide))
        (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
        (by decide)) (TAlphaVar.here _ _ _))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective
        (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) (by decide))
        (freshVar_injective (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv)
        (by decide)) (TAlphaVar.here _ _ _))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg split_alpha_0002))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg split_alpha_0002))))))))))))))
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective
                  (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
                  (by decide)) (freshVar_injective
                  (((syn_cvv)).fv ∪ ((syn_csn (syn_csn (Class.cv x)))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab
              (TAlphaWff.objEq (TAlphaVar.here _ _ _) (TAlphaVar.here _ _ _))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 2))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 2)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 1))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 1))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex
                              (TAlphaWff.ex (TAlphaWff.neg split_alpha_0001)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_fv_fresh _ _ (by
                              intro a b h hne;
                              simp only [List.mem_cons, List.not_mem_nil, or_false,
                                Prod.mk.injEq] at h;
                              repeat'
                                (first
                                  | (rcases h with ⟨rfl, rfl⟩));
                                all_goals aesop)))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex
                              (TAlphaWff.ex (TAlphaWff.neg split_alpha_0001)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.refl_of_fv_fresh _ _ (by
                              intro a b h hne;
                              simp only [List.mem_cons, List.not_mem_nil, or_false,
                                Prod.mk.injEq] at h;
                              repeat'
                                (first
                                  | (rcases h with ⟨rfl, rfl⟩));
                                all_goals aesop)))))))))) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg split_alpha_0003))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
