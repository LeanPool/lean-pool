/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001016Ins3k. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_ins3k`. -/
@[expose]
noncomputable def nominalDfIns3k (x : Var) (y : Var) (z : Var) (v : Var) (u : Var)
    (t : Var) (A : Class) (dv_A_t : t ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_t_u : t ≠ u)
    (dv_t_v : t ≠ v) (_dv_t_x : t ≠ x) (dv_t_y : t ≠ y) (dv_t_z : t ≠ z) (dv_u_v : u ≠ v)
    (_dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_u_z : u ≠ z) (_dv_v_x : v ≠ x) (dv_v_y : v ≠ y)
    (dv_v_z : v ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCins3k A) (.cab x (synWex y (synWex z
              (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex t (synWex u
                    (synWex v (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
                        (.classEq (.cv z) (synCopk (.cv u) (.cv v)))
                        (.classMem (synCopk (.cv t) (.cv u)) A)))))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv) 1)
  let alphaDummy002 : Var := (freshVar ((A).fv) 2)
  let alphaDummy003 : Var := (freshVar ((A).fv) 3)
  let alphaDummy004 : Var := (freshVar ((A).fv) 4)
  let alphaDummy005 : Var := (freshVar ((A).fv) 5)
  let alphaDummy006 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy004))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))))).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv y))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alphaDummy008 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy004)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy004)))).fv) 0)
  let alphaDummy009 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) 0)
  let alphaDummy010 : Var := (freshVar (((synCsn (Class.cv alphaDummy004))).fv) 0)
  let alphaDummy011 : Var := (freshVar (((synCsn (Class.cv y))).fv) 0)
  let alphaDummy012 : Var := (freshVar (((Class.cv alphaDummy004)).fv) 0)
  let alphaDummy013 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv ∪
        ((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))).fv) 0)
  let alphaDummy017 : Var := (freshVar (((synCpr (Class.cv y) (Class.cv z))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy005)))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv y)))).fv ∪
        ((synCcompl (synCsn (Class.cv z)))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy004))).fv ∪
        ((synCsn (Class.cv alphaDummy004))).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy005))).fv ∪
        ((synCsn (Class.cv alphaDummy005))).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) 0)
  let alphaDummy024 : Var := (freshVar (((Class.cv alphaDummy005)).fv) 0)
  let alphaDummy025 : Var := (freshVar (((Class.cv z)).fv) 0)
  let alphaDummy026 : Var := (freshVar (((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy027 : Var := (freshVar (((synCsn (Class.cv t))).fv) 0)
  let alphaDummy028 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy029 : Var := (freshVar (((Class.cv t)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv u))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv u) (Class.cv v))))).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy033 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv u)))).fv ∪ ((synCsn (synCsn (Class.cv u)))).fv) 0)
  let alphaDummy034 : Var := (freshVar (((synCsn (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy035 : Var := (freshVar (((synCsn (Class.cv u))).fv) 0)
  let alphaDummy036 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy037 : Var := (freshVar (((Class.cv u)).fv) 0)
  let alphaDummy038 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) 0)
  let alphaDummy039 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv ∪
        ((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv) 0)
  let alphaDummy040 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy041 : Var := (freshVar (((synCpr (Class.cv u) (Class.cv v))).fv) 0)
  let alphaDummy042 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) 0)
  let alphaDummy043 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv u)))).fv ∪
        ((synCcompl (synCsn (Class.cv v)))).fv) 0)
  let alphaDummy044 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy001))).fv ∪
        ((synCsn (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy045 : Var :=
    (freshVar (((synCsn (Class.cv u))).fv ∪ ((synCsn (Class.cv u))).fv) 0)
  let alphaDummy046 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy002))).fv ∪
        ((synCsn (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy047 : Var :=
    (freshVar (((synCsn (Class.cv v))).fv ∪ ((synCsn (Class.cv v))).fv) 0)
  let alphaDummy048 : Var := (freshVar (((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy049 : Var := (freshVar (((Class.cv v)).fv) 0)
  let alphaDummy050 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) 0)
  let alphaDummy051 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv t))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) 0)
  let alphaDummy052 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) 0)
  let alphaDummy053 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv t)))).fv ∪ ((synCsn (synCsn (Class.cv t)))).fv) 0)
  let alphaDummy054 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy055 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv ∪
        ((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) 0)
  let alphaDummy056 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy057 : Var := (freshVar (((synCpr (Class.cv t) (Class.cv u))).fv) 0)
  let alphaDummy058 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy059 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv t)))).fv ∪
        ((synCcompl (synCsn (Class.cv u)))).fv) 0)
  let alphaDummy060 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy000))).fv ∪
        ((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy061 : Var :=
    (freshVar (((synCsn (Class.cv t))).fv ∪ ((synCsn (Class.cv t))).fv) 0)
  have fresh_056 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_057 : alphaDummy001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  have fresh_058 : alphaDummy002 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 2
  have fresh_059 : alphaDummy003 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 3
  have fresh_060 : alphaDummy004 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 4
  have fresh_061 : alphaDummy005 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 5
  have support_part_0000 :
    alphaDummy004 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy004))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alphaDummy004 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy004))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))))).fv)
        support_part_0000)
  have support_part_0001 : y ∈ (((synCcompl (synCsn (synCsn (Class.cv y))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0001 :
    y ∈
      (((synCcompl (synCsn (synCsn (Class.cv y))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv)
        support_part_0001)
  have support_part_0002 :
    alphaDummy004 ∈ (((synCsn (synCsn (Class.cv alphaDummy004)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alphaDummy004 ∈
      (((synCsn (synCsn (Class.cv alphaDummy004)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy004)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy004)))).fv)
        support_part_0002)
  have support_part_0003 : y ∈ (((synCsn (synCsn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    y ∈ (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy004 ∈ (((synCsn (Class.cv alphaDummy004))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alphaDummy004 ∈ (((synCsn (Class.cv alphaDummy004))).fv) :=
    by exact support_part_0004
  have support_part_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by exact support_part_0005
  have support_part_0006 : alphaDummy004 ∈ (((Class.cv alphaDummy004)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alphaDummy004 ∈ (((Class.cv alphaDummy004)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by exact support_part_0007
  have support_part_0008 :
    alphaDummy004 ∈
      (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alphaDummy004 ∈
      (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv)
        support_part_0008)
  have support_part_0009 : y ∈ (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0009 :
    y ∈
      (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv ∪
        ((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv)
        support_part_0009)
  have support_part_0010 :
    alphaDummy004 ∈
      (((synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy004 ∈
      (((synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))).fv) :=
    by exact support_part_0010
  have support_part_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alphaDummy004 ∈ (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alphaDummy004 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy005)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy005)))).fv)
        support_part_0012)
  have support_part_0013 : y ∈ (((synCcompl (synCsn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0013 :
    y ∈
      (((synCcompl (synCsn (Class.cv y)))).fv ∪ ((synCcompl (synCsn (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv z)))).fv) support_part_0013)
  have support_part_0014 :
    alphaDummy004 ∈ (((synCsn (Class.cv alphaDummy004))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alphaDummy004 ∈
      (((synCsn (Class.cv alphaDummy004))).fv ∪ ((synCsn (Class.cv alphaDummy004))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy004))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    y ∈ (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy005 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alphaDummy005 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy004))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy004))))).fv)
        support_part_0016)
  have support_part_0017 :
    z ∈ (((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0017 :
    z ∈
      (((synCcompl (synCsn (synCsn (Class.cv y))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv y))))).fv)
        support_part_0017)
  have support_part_0018 :
    alphaDummy005 ∈
      (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alphaDummy005 ∈
      (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005)))).fv)
        support_part_0018)
  have support_part_0019 : z ∈ (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0019 :
    z ∈
      (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv ∪
        ((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv)
        support_part_0019)
  have support_part_0020 :
    alphaDummy005 ∈
      (((synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy005 ∈
      (((synCpr (Class.cv alphaDummy004) (Class.cv alphaDummy005))).fv) :=
    by exact support_part_0020
  have support_part_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alphaDummy005 ∈ (((synCcompl (synCsn (Class.cv alphaDummy005)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alphaDummy005 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy005)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv)
        support_part_0022)
  have support_part_0023 : z ∈ (((synCcompl (synCsn (Class.cv z)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0023 :
    z ∈
      (((synCcompl (synCsn (Class.cv y)))).fv ∪ ((synCcompl (synCsn (Class.cv z)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv y)))).fv) support_part_0023)
  have support_part_0024 :
    alphaDummy005 ∈ (((synCsn (Class.cv alphaDummy005))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alphaDummy005 ∈
      (((synCsn (Class.cv alphaDummy005))).fv ∪ ((synCsn (Class.cv alphaDummy005))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy005))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((synCsn (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    z ∈ (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by exact support_part_0027
  have support_part_0028 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0028 : alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) :=
    by exact support_part_0028
  have support_part_0029 : t ∈ (((synCsn (Class.cv t))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0029 : t ∈ (((synCsn (Class.cv t))).fv) := by exact support_part_0029
  have support_part_0030 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0030 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    exact support_part_0030
  have support_part_0031 : t ∈ (((Class.cv t)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0031 : t ∈ (((Class.cv t)).fv) := by exact support_part_0031
  have support_part_0032 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0032 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv)
        support_part_0032)
  have support_part_0033 : u ∈ (((synCcompl (synCsn (synCsn (Class.cv u))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0033 :
    u ∈
      (((synCcompl (synCsn (synCsn (Class.cv u))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv u) (Class.cv v))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (synCpr (Class.cv u) (Class.cv v))))).fv)
        support_part_0033)
  have support_part_0034 :
    alphaDummy001 ∈ (((synCsn (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0034 :
    alphaDummy001 ∈
      (((synCsn (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy001)))).fv)
        support_part_0034)
  have support_part_0035 : u ∈ (((synCsn (synCsn (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0035 :
    u ∈ (((synCsn (synCsn (Class.cv u)))).fv ∪ ((synCsn (synCsn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv u)))).fv) support_part_0035)
  have support_part_0036 :
    alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0036 : alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0036
  have support_part_0037 : u ∈ (((synCsn (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0037 : u ∈ (((synCsn (Class.cv u))).fv) := by exact support_part_0037
  have support_part_0038 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0038 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0038
  have support_part_0039 : u ∈ (((Class.cv u)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0039 : u ∈ (((Class.cv u)).fv) := by exact support_part_0039
  have support_part_0040 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0040 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv)
        support_part_0040)
  have support_part_0041 : u ∈ (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0041 :
    u ∈
      (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv ∪
        ((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv)
        support_part_0041)
  have support_part_0042 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0042 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by exact support_part_0042
  have support_part_0043 : u ∈ (((synCpr (Class.cv u) (Class.cv v))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0043 : u ∈ (((synCpr (Class.cv u) (Class.cv v))).fv) := by
    exact support_part_0043
  have support_part_0044 :
    alphaDummy001 ∈ (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0044 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv)
        support_part_0044)
  have support_part_0045 : u ∈ (((synCcompl (synCsn (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0045 :
    u ∈
      (((synCcompl (synCsn (Class.cv u)))).fv ∪ ((synCcompl (synCsn (Class.cv v)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv v)))).fv) support_part_0045)
  have support_part_0046 :
    alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0046 :
    alphaDummy001 ∈
      (((synCsn (Class.cv alphaDummy001))).fv ∪ ((synCsn (Class.cv alphaDummy001))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy001))).fv) support_part_0046)
  have support_part_0047 : u ∈ (((synCsn (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0047 :
    u ∈ (((synCsn (Class.cv u))).fv ∪ ((synCsn (Class.cv u))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv u))).fv) support_part_0047)
  have support_part_0048 :
    alphaDummy002 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0048 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv)
        support_part_0048)
  have support_part_0049 :
    v ∈ (((synCcompl (synCsn (synCpr (Class.cv u) (Class.cv v))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0049 :
    v ∈
      (((synCcompl (synCsn (synCsn (Class.cv u))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv u) (Class.cv v))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv u))))).fv)
        support_part_0049)
  have support_part_0050 :
    alphaDummy002 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0050 :
    alphaDummy002 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv)
        support_part_0050)
  have support_part_0051 : v ∈ (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0051 :
    v ∈
      (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv ∪
        ((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv u) (Class.cv v)))).fv)
        support_part_0051)
  have support_part_0052 :
    alphaDummy002 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0052 :
    alphaDummy002 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by exact support_part_0052
  have support_part_0053 : v ∈ (((synCpr (Class.cv u) (Class.cv v))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0053 : v ∈ (((synCpr (Class.cv u) (Class.cv v))).fv) := by
    exact support_part_0053
  have support_part_0054 :
    alphaDummy002 ∈ (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0054 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv)
        support_part_0054)
  have support_part_0055 : v ∈ (((synCcompl (synCsn (Class.cv v)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0055 :
    v ∈
      (((synCcompl (synCsn (Class.cv u)))).fv ∪ ((synCcompl (synCsn (Class.cv v)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv u)))).fv) support_part_0055)
  have support_part_0056 :
    alphaDummy002 ∈ (((synCsn (Class.cv alphaDummy002))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0056 :
    alphaDummy002 ∈
      (((synCsn (Class.cv alphaDummy002))).fv ∪ ((synCsn (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy002))).fv) support_part_0056)
  have support_part_0057 : v ∈ (((synCsn (Class.cv v))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0057 :
    v ∈ (((synCsn (Class.cv v))).fv ∪ ((synCsn (Class.cv v))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv v))).fv) support_part_0057)
  have support_part_0058 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0058 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    exact support_part_0058
  have support_part_0059 : v ∈ (((Class.cv v)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0059 : v ∈ (((Class.cv v)).fv) := by exact support_part_0059
  have support_part_0060 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0060 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv)
        support_part_0060)
  have support_part_0061 : t ∈ (((synCcompl (synCsn (synCsn (Class.cv t))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0061 :
    t ∈
      (((synCcompl (synCsn (synCsn (Class.cv t))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv)
        support_part_0061)
  have support_part_0062 :
    alphaDummy000 ∈ (((synCsn (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0062 :
    alphaDummy000 ∈
      (((synCsn (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
        support_part_0062)
  have support_part_0063 : t ∈ (((synCsn (synCsn (Class.cv t)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0063 :
    t ∈ (((synCsn (synCsn (Class.cv t)))).fv ∪ ((synCsn (synCsn (Class.cv t)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv t)))).fv) support_part_0063)
  have support_part_0064 :
    alphaDummy000 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0064 :
    alphaDummy000 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv)
        support_part_0064)
  have support_part_0065 : t ∈ (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0065 :
    t ∈
      (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv ∪
        ((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv)
        support_part_0065)
  have support_part_0066 :
    alphaDummy000 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0066 :
    alphaDummy000 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0066
  have support_part_0067 : t ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0067 : t ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    exact support_part_0067
  have support_part_0068 :
    alphaDummy000 ∈ (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0068 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv)
        support_part_0068)
  have support_part_0069 : t ∈ (((synCcompl (synCsn (Class.cv t)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0069 :
    t ∈
      (((synCcompl (synCsn (Class.cv t)))).fv ∪ ((synCcompl (synCsn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv u)))).fv) support_part_0069)
  have support_part_0070 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0070 :
    alphaDummy000 ∈
      (((synCsn (Class.cv alphaDummy000))).fv ∪ ((synCsn (Class.cv alphaDummy000))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy000))).fv) support_part_0070)
  have support_part_0071 : t ∈ (((synCsn (Class.cv t))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0071 :
    t ∈ (((synCsn (Class.cv t))).fv ∪ ((synCsn (Class.cv t))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv t))).fv) support_part_0071)
  have support_part_0072 :
    alphaDummy001 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0072 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv)
        support_part_0072)
  have support_part_0073 :
    u ∈ (((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0073 :
    u ∈
      (((synCcompl (synCsn (synCsn (Class.cv t))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv t))))).fv)
        support_part_0073)
  have support_part_0074 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0074 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv)
        support_part_0074)
  have support_part_0075 : u ∈ (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0075 :
    u ∈
      (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv ∪
        ((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv)
        support_part_0075)
  have support_part_0076 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0076 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0076
  have support_part_0077 : u ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0077 : u ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    exact support_part_0077
  have support_part_0078 :
    alphaDummy001 ∈ (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0078 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv)
        support_part_0078)
  have support_part_0079 : u ∈ (((synCcompl (synCsn (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0079 :
    u ∈
      (((synCcompl (synCsn (Class.cv t)))).fv ∪ ((synCcompl (synCsn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv t)))).fv) support_part_0079)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy018, alphaDummy019), (alphaDummy016, alphaDummy017),
        (alphaDummy014, alphaDummy015), (alphaDummy006, alphaDummy007),
        (alphaDummy005, z), (alphaDummy004, y), (alphaDummy003, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy018)
          (synCcompl (synCsn (Class.cv alphaDummy004)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy018)
            (synCcompl (synCsn (Class.cv alphaDummy005))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy019) (synCcompl (synCsn (Class.cv y))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy019)
            (synCcompl (synCsn (Class.cv z)))))) :=
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
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy042, alphaDummy043), (alphaDummy040, alphaDummy041),
        (alphaDummy038, alphaDummy039), (alphaDummy030, alphaDummy031),
        (alphaDummy002, v), (alphaDummy001, u), (alphaDummy000, t),
        (alphaDummy005, z), (alphaDummy004, y), (alphaDummy003, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy042)
          (synCcompl (synCsn (Class.cv alphaDummy001)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy042)
            (synCcompl (synCsn (Class.cv alphaDummy002))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy043) (synCcompl (synCsn (Class.cv u))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy043)
            (synCcompl (synCsn (Class.cv v)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                    (TAlphaVar.here _ _ _))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                    (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                                    (TAlphaVar.here _ _ _)))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0058 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0059 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0))
                                    (TAlphaVar.here _ _ _)))))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy058, alphaDummy059), (alphaDummy056, alphaDummy057),
        (alphaDummy054, alphaDummy055), (alphaDummy050, alphaDummy051),
        (alphaDummy002, v), (alphaDummy001, u), (alphaDummy000, t),
        (alphaDummy005, z), (alphaDummy004, y), (alphaDummy003, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy058)
          (synCcompl (synCsn (Class.cv alphaDummy000)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy058)
            (synCcompl (synCsn (Class.cv alphaDummy001))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy059) (synCcompl (synCsn (Class.cv t))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy059)
            (synCcompl (synCsn (Class.cv u)))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_t_v
                                    (TAlphaVar.there
                                      (freshVar_injective ((A).fv) (by decide)) dv_t_u
                                      (TAlphaVar.here _ _ _)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0070 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0071 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0068 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0069 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0066 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0067 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0064 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0065 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0060 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0061 0))
                                  (TAlphaVar.there
                                    (freshVar_injective ((A).fv) (by decide)) dv_t_v
                                    (TAlphaVar.there
                                      (freshVar_injective ((A).fv) (by decide)) dv_t_u
                                      (TAlphaVar.here _ _ _))))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0079 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0077 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0073 0))
                                    (TAlphaVar.there
                                      (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                      (TAlphaVar.here _ _ _))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0078 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0079 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0076 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0077 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0074 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar support_mem_0075 0))
                                  (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0072 0))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0073 0))
                                    (TAlphaVar.there
                                      (freshVar_injective ((A).fv) (by decide)) dv_u_v
                                      (TAlphaVar.here _ _ _))))))))))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy002, v), (alphaDummy001, u), (alphaDummy000, t),
        (alphaDummy005, z), (alphaDummy004, y), (alphaDummy003, x)]
      (Wff.imp (synWa (Wff.classEq (Class.cv alphaDummy004)
            (synCsn (synCsn (Class.cv alphaDummy000))))
          (Wff.classEq (Class.cv alphaDummy005)
            (synCopk (Class.cv alphaDummy001) (Class.cv alphaDummy002)))) (Wff.neg
          (Wff.classMem (synCopk (Class.cv alphaDummy000) (Class.cv alphaDummy001)) A)))
      (Wff.imp (synWa (Wff.classEq (Class.cv y) (synCsn (synCsn (Class.cv t))))
          (Wff.classEq (Class.cv z) (synCopk (Class.cv u) (Class.cv v))))
        (Wff.neg (Wff.classMem (synCopk (Class.cv t) (Class.cv u)) A))) :=
    (TAlphaWff.imp (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_v_y)
              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_u_y)
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_t_y)
                  (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_y_z
                    (TAlphaVar.here _ _ _)))))) (TAlphaClass.cab
            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
                        (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_t_v
                          (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                            dv_t_u (TAlphaVar.here _ _ _))))))))))) (TAlphaWff.classEq
          (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_v_z)
              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_u_z)
                (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                  (Ne.symm dv_t_z) (TAlphaVar.here _ _ _))))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0036 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0037 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0034 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0035 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0032 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_u_v (TAlphaVar.here _ _ _))))))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.neg splitAlpha0001))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg splitAlpha0001))))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0062 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0063 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0060 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_t_v (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_t_u (TAlphaVar.here _ _ _)))))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cv (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0062 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0063 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0060 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0061 0)) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_t_v (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) dv_t_u (TAlphaVar.here _ _ _)))))))))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.neg (TAlphaWff.neg splitAlpha0002))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg
                                  (TAlphaWff.neg splitAlpha0002)))))))))))))
          (TAlphaClass.reflOfFvFresh _ _ (TEnvFresh.cons fresh_058 dv_A_v
              (TEnvFresh.cons fresh_057 dv_A_u (TEnvFresh.cons fresh_056 dv_A_t
                  (TEnvFresh.cons fresh_061 dv_A_z (TEnvFresh.cons fresh_060 dv_A_y
                      (TEnvFresh.cons fresh_059 dv_A_x ((by simp [TEnvFresh]))))))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_z
                    (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((A).fv)
        (by decide)) dv_y_z (TAlphaVar.here _ _ _))))))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there (freshVar_injective ((A).fv)
        (by decide)) dv_y_z (TAlphaVar.here _ _ _))))))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.neg splitAlpha0000))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg splitAlpha0000))))))))))))))
              (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg splitAlpha0003))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
