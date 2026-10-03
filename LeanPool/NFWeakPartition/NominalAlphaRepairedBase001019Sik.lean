/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001019Sik. -/


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
noncomputable def nominal_df_sik (x : Var) (y : Var) (z : Var) (u : Var) (t : Var)
    (A : Class) (dv_A_t : t ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_t_u : t ≠ u) (__dv_t_x : t ≠ x)
    (dv_t_y : t ≠ y) (dv_t_z : t ≠ z) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_u_z : u ≠ z)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_csik A) (.cab x (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex t (syn_wex u
                    (syn_w3a (.classEq (.cv y) (syn_csn (.cv t)))
                      (.classEq (.cv z) (syn_csn (.cv u)))
                      (.classMem (syn_copk (.cv t) (.cv u)) A))))))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv) 1)
  let alpha_dummy_002 : Var := (freshVar ((A).fv) 2)
  let alpha_dummy_003 : Var := (freshVar ((A).fv) 3)
  let alpha_dummy_004 : Var := (freshVar ((A).fv) 4)
  let alpha_dummy_005 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_003))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))))).fv) 0)
  let alpha_dummy_006 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alpha_dummy_007 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_003)))).fv) 0)
  let alpha_dummy_008 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_003))).fv) 0)
  let alpha_dummy_010 : Var := (freshVar (((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_011 : Var := (freshVar (((Class.cv alpha_dummy_003)).fv) 0)
  let alpha_dummy_012 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alpha_dummy_013 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv) 0)
  let alpha_dummy_014 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alpha_dummy_015 : Var :=
    (freshVar (((syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((syn_cpr (Class.cv y) (Class.cv z))).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_004)))).fv) 0)
  let alpha_dummy_018 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv z)))).fv) 0)
  let alpha_dummy_019 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_003))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_003))).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_004))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_004))).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) 0)
  let alpha_dummy_023 : Var := (freshVar (((Class.cv alpha_dummy_004)).fv) 0)
  let alpha_dummy_024 : Var := (freshVar (((Class.cv z)).fv) 0)
  let alpha_dummy_025 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_026 : Var := (freshVar (((Class.cv t)).fv) 0)
  let alpha_dummy_027 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_028 : Var := (freshVar (((Class.cv u)).fv) 0)
  let alpha_dummy_029 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))))).fv) 0)
  let alpha_dummy_030 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv t))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv t) (Class.cv u))))).fv) 0)
  let alpha_dummy_031 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) 0)
  let alpha_dummy_032 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv t)))).fv ∪ ((syn_csn (syn_csn (Class.cv t)))).fv) 0)
  let alpha_dummy_033 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_034 : Var := (freshVar (((syn_csn (Class.cv t))).fv) 0)
  let alpha_dummy_035 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv) 0)
  let alpha_dummy_036 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv) 0)
  let alpha_dummy_037 : Var :=
    (freshVar (((syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_038 : Var := (freshVar (((syn_cpr (Class.cv t) (Class.cv u))).fv) 0)
  let alpha_dummy_039 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) 0)
  let alpha_dummy_040 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv t)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv u)))).fv) 0)
  let alpha_dummy_041 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_000))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_042 : Var :=
    (freshVar (((syn_csn (Class.cv t))).fv ∪ ((syn_csn (Class.cv t))).fv) 0)
  let alpha_dummy_043 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_001))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_044 : Var :=
    (freshVar (((syn_csn (Class.cv u))).fv ∪ ((syn_csn (Class.cv u))).fv) 0)
  have fresh_040 : alpha_dummy_000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_041 : alpha_dummy_001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  have fresh_042 : alpha_dummy_002 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 2
  have fresh_043 : alpha_dummy_003 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 3
  have fresh_044 : alpha_dummy_004 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 4
  have support_part_0000 :
    alpha_dummy_003 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_003))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alpha_dummy_003 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_003))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))))).fv)
        support_part_0000)
  have support_part_0001 : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0001 :
    y ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv)
        support_part_0001)
  have support_part_0002 :
    alpha_dummy_003 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_003)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alpha_dummy_003 ∈
      (((syn_csn (syn_csn (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_003)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_003)))).fv)
        support_part_0002)
  have support_part_0003 : y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 :
    alpha_dummy_003 ∈ (((syn_csn (Class.cv alpha_dummy_003))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alpha_dummy_003 ∈ (((syn_csn (Class.cv alpha_dummy_003))).fv) :=
    by exact support_part_0004
  have support_part_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by exact support_part_0005
  have support_part_0006 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_003)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alpha_dummy_003 ∈ (((Class.cv alpha_dummy_003)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by exact support_part_0007
  have support_part_0008 :
    alpha_dummy_003 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alpha_dummy_003 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv)
        support_part_0008)
  have support_part_0009 : y ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0009 :
    y ∈
      (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv)
        support_part_0009)
  have support_part_0010 :
    alpha_dummy_003 ∈
      (((syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alpha_dummy_003 ∈
      (((syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))).fv) :=
    by exact support_part_0010
  have support_part_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alpha_dummy_003 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alpha_dummy_003 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_004)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_004)))).fv)
        support_part_0012)
  have support_part_0013 : y ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0013 :
    y ∈
      (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv z)))).fv) support_part_0013)
  have support_part_0014 :
    alpha_dummy_003 ∈ (((syn_csn (Class.cv alpha_dummy_003))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alpha_dummy_003 ∈
      (((syn_csn (Class.cv alpha_dummy_003))).fv ∪ ((syn_csn (Class.cv alpha_dummy_003))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_003))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 :
    alpha_dummy_004 ∈
      (((syn_ccompl (syn_csn
            (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alpha_dummy_004 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_003))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_003))))).fv)
        support_part_0016)
  have support_part_0017 :
    z ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0017 :
    z ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv z))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv)
        support_part_0017)
  have support_part_0018 :
    alpha_dummy_004 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alpha_dummy_004 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004)))).fv)
        support_part_0018)
  have support_part_0019 : z ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0019 :
    z ∈
      (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv z)))).fv)
        support_part_0019)
  have support_part_0020 :
    alpha_dummy_004 ∈
      (((syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alpha_dummy_004 ∈
      (((syn_cpr (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))).fv) :=
    by exact support_part_0020
  have support_part_0021 : z ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : z ∈ (((syn_cpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alpha_dummy_004 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_004)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alpha_dummy_004 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_004)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))).fv)
        support_part_0022)
  have support_part_0023 : z ∈ (((syn_ccompl (syn_csn (Class.cv z)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0023 :
    z ∈
      (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv y)))).fv) support_part_0023)
  have support_part_0024 :
    alpha_dummy_004 ∈ (((syn_csn (Class.cv alpha_dummy_004))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alpha_dummy_004 ∈
      (((syn_csn (Class.cv alpha_dummy_004))).fv ∪ ((syn_csn (Class.cv alpha_dummy_004))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_004))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((syn_csn (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    z ∈ (((syn_csn (Class.cv z))).fv ∪ ((syn_csn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alpha_dummy_004 ∈ (((Class.cv alpha_dummy_004)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alpha_dummy_004 ∈ (((Class.cv alpha_dummy_004)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by exact support_part_0027
  have support_part_0028 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0028 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    exact support_part_0028
  have support_part_0029 : t ∈ (((Class.cv t)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0029 : t ∈ (((Class.cv t)).fv) := by exact support_part_0029
  have support_part_0030 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0030 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0030
  have support_part_0031 : u ∈ (((Class.cv u)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0031 : u ∈ (((Class.cv u)).fv) := by exact support_part_0031
  have support_part_0032 :
    alpha_dummy_000 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0032 :
    alpha_dummy_000 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))))).fv)
        support_part_0032)
  have support_part_0033 : t ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv t))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0033 :
    t ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv t))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv t) (Class.cv u))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv t) (Class.cv u))))).fv)
        support_part_0033)
  have support_part_0034 :
    alpha_dummy_000 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0034 :
    alpha_dummy_000 ∈
      (((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_000)))).fv)
        support_part_0034)
  have support_part_0035 : t ∈ (((syn_csn (syn_csn (Class.cv t)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0035 :
    t ∈ (((syn_csn (syn_csn (Class.cv t)))).fv ∪ ((syn_csn (syn_csn (Class.cv t)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv t)))).fv) support_part_0035)
  have support_part_0036 :
    alpha_dummy_000 ∈ (((syn_csn (Class.cv alpha_dummy_000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0036 : alpha_dummy_000 ∈ (((syn_csn (Class.cv alpha_dummy_000))).fv) :=
    by exact support_part_0036
  have support_part_0037 : t ∈ (((syn_csn (Class.cv t))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0037 : t ∈ (((syn_csn (Class.cv t))).fv) := by exact support_part_0037
  have support_part_0038 :
    alpha_dummy_000 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0038 :
    alpha_dummy_000 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv)
        support_part_0038)
  have support_part_0039 : t ∈ (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0039 :
    t ∈
      (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv)
        support_part_0039)
  have support_part_0040 :
    alpha_dummy_000 ∈
      (((syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0040 :
    alpha_dummy_000 ∈
      (((syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))).fv) :=
    by exact support_part_0040
  have support_part_0041 : t ∈ (((syn_cpr (Class.cv t) (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0041 : t ∈ (((syn_cpr (Class.cv t) (Class.cv u))).fv) := by
    exact support_part_0041
  have support_part_0042 :
    alpha_dummy_000 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0042 :
    alpha_dummy_000 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv)
        support_part_0042)
  have support_part_0043 : t ∈ (((syn_ccompl (syn_csn (Class.cv t)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0043 :
    t ∈
      (((syn_ccompl (syn_csn (Class.cv t)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv u)))).fv) support_part_0043)
  have support_part_0044 :
    alpha_dummy_000 ∈ (((syn_csn (Class.cv alpha_dummy_000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0044 :
    alpha_dummy_000 ∈
      (((syn_csn (Class.cv alpha_dummy_000))).fv ∪ ((syn_csn (Class.cv alpha_dummy_000))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_000))).fv) support_part_0044)
  have support_part_0045 : t ∈ (((syn_csn (Class.cv t))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0045 :
    t ∈ (((syn_csn (Class.cv t))).fv ∪ ((syn_csn (Class.cv t))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv t))).fv) support_part_0045)
  have support_part_0046 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_csn
            (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0046 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_000))))).fv)
        support_part_0046)
  have support_part_0047 :
    u ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv t) (Class.cv u))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0047 :
    u ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv t))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv t) (Class.cv u))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv t))))).fv)
        support_part_0047)
  have support_part_0048 :
    alpha_dummy_001 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0048 :
    alpha_dummy_001 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)))).fv)
        support_part_0048)
  have support_part_0049 : u ∈ (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0049 :
    u ∈
      (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv t) (Class.cv u)))).fv)
        support_part_0049)
  have support_part_0050 :
    alpha_dummy_001 ∈
      (((syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0050 :
    alpha_dummy_001 ∈
      (((syn_cpr (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001))).fv) :=
    by exact support_part_0050
  have support_part_0051 : u ∈ (((syn_cpr (Class.cv t) (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0051 : u ∈ (((syn_cpr (Class.cv t) (Class.cv u))).fv) := by
    exact support_part_0051
  have support_part_0052 :
    alpha_dummy_001 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0052 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv)
        support_part_0052)
  have support_part_0053 : u ∈ (((syn_ccompl (syn_csn (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0053 :
    u ∈
      (((syn_ccompl (syn_csn (Class.cv t)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv t)))).fv) support_part_0053)
  have support_part_0054 :
    alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0054 :
    alpha_dummy_001 ∈
      (((syn_csn (Class.cv alpha_dummy_001))).fv ∪ ((syn_csn (Class.cv alpha_dummy_001))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_001))).fv) support_part_0054)
  have support_part_0055 : u ∈ (((syn_csn (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0055 :
    u ∈ (((syn_csn (Class.cv u))).fv ∪ ((syn_csn (Class.cv u))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv u))).fv) support_part_0055)
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_017, alpha_dummy_018), (alpha_dummy_015, alpha_dummy_016),
        (alpha_dummy_013, alpha_dummy_014), (alpha_dummy_005, alpha_dummy_006),
        (alpha_dummy_004, z), (alpha_dummy_003, y), (alpha_dummy_002, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_017)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_003)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_017)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_004))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_018) (syn_ccompl (syn_csn (Class.cv y))))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_018)
            (syn_ccompl (syn_csn (Class.cv z)))))) :=
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
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_y_z
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
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_y_z
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
      [(alpha_dummy_039, alpha_dummy_040), (alpha_dummy_037, alpha_dummy_038),
        (alpha_dummy_035, alpha_dummy_036), (alpha_dummy_029, alpha_dummy_030),
        (alpha_dummy_001, u), (alpha_dummy_000, t), (alpha_dummy_004, z),
        (alpha_dummy_003, y), (alpha_dummy_002, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_039)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_039)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_001))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_040) (syn_ccompl (syn_csn (Class.cv t))))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_040)
            (syn_ccompl (syn_csn (Class.cv u)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_t_u
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_t_u
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
                                    (TAlphaVar.here _ _ _)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
                                    (TAlphaVar.here _ _ _)))))))))))))))))
  have split_alpha_0002 :
    TAlphaWff [(alpha_dummy_004, z), (alpha_dummy_003, y), (alpha_dummy_002, x)]
      (Wff.imp (Wff.classEq (Class.cv alpha_dummy_002)
          (syn_copk (Class.cv alpha_dummy_003) (Class.cv alpha_dummy_004))) (Wff.neg
          (syn_wex alpha_dummy_000 (syn_wex alpha_dummy_001 (syn_w3a
                (Wff.classEq (Class.cv alpha_dummy_003) (syn_csn (Class.cv alpha_dummy_000)))
                (Wff.classEq (Class.cv alpha_dummy_004) (syn_csn (Class.cv alpha_dummy_001)))
                (Wff.classMem
                  (syn_copk (Class.cv alpha_dummy_000) (Class.cv alpha_dummy_001)) A))))))
      (Wff.imp (Wff.classEq (Class.cv x) (syn_copk (Class.cv y) (Class.cv z))) (Wff.neg
          (syn_wex t (syn_wex u (syn_w3a (Wff.classEq (Class.cv y) (syn_csn (Class.cv t)))
                (Wff.classEq (Class.cv z) (syn_csn (Class.cv u)))
                (Wff.classMem (syn_copk (Class.cv t) (Class.cv u)) A)))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_z
            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
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
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_y_z (TAlphaVar.here _ _ _))))))))))))
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
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_y_z (TAlphaVar.here _ _ _))))))))))))))))
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
      (TAlphaWff.neg (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.conj
                (TAlphaWff.classEq (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_u_y)
                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                        (Ne.symm dv_t_y)
                        (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_y_z
                          (TAlphaVar.here _ _ _))))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                            dv_t_u (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                  (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                      (Ne.symm dv_u_z)
                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                        (Ne.symm dv_t_z) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classMem (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there (freshVar_injective ((A).fv)
        (by decide)) dv_t_u (TAlphaVar.here _ _ _))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there (freshVar_injective ((A).fv)
        (by decide)) dv_t_u (TAlphaVar.here _ _ _))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg split_alpha_0001))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg split_alpha_0001)))))))))))))
                (TAlphaClass.refl_of_fv_fresh _ _ (by
                    intro a b h hne;
                    simp only [List.mem_cons, List.not_mem_nil, or_false,
                      Prod.mk.injEq] at h;
                    repeat'
                      (first
                        | (rcases h with ⟨rfl, rfl⟩));
                      all_goals aesop))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg split_alpha_0002))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
