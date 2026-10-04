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

/-- Checked nominal proof certificate identified upstream as `nominal_df_sik`. -/
@[expose]
noncomputable def nominalDfSik (x : Var) (y : Var) (z : Var) (u : Var) (t : Var)
    (A : Class) (dv_A_t : t ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_t_u : t ≠ u) (__dv_t_x : t ≠ x)
    (dv_t_y : t ≠ y) (dv_t_z : t ≠ z) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_u_z : u ≠ z)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCsik A) (.cab x (synWex y (synWex z
              (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex t (synWex u
                    (synW3a (.classEq (.cv y) (synCsn (.cv t)))
                      (.classEq (.cv z) (synCsn (.cv u)))
                      (.classMem (synCopk (.cv t) (.cv u)) A))))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv) 1)
  let alphaDummy002 : Var := (freshVar ((A).fv) 2)
  let alphaDummy003 : Var := (freshVar ((A).fv) 3)
  let alphaDummy004 : Var := (freshVar ((A).fv) 4)
  let alphaDummy005 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy003))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv y))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy003)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy003)))).fv) 0)
  let alphaDummy008 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) 0)
  let alphaDummy009 : Var := (freshVar (((synCsn (Class.cv alphaDummy003))).fv) 0)
  let alphaDummy010 : Var := (freshVar (((synCsn (Class.cv y))).fv) 0)
  let alphaDummy011 : Var := (freshVar (((Class.cv alphaDummy003)).fv) 0)
  let alphaDummy012 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv ∪
        ((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))).fv) 0)
  let alphaDummy016 : Var := (freshVar (((synCpr (Class.cv y) (Class.cv z))).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy004)))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv y)))).fv ∪
        ((synCcompl (synCsn (Class.cv z)))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy003))).fv ∪
        ((synCsn (Class.cv alphaDummy003))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy004))).fv ∪
        ((synCsn (Class.cv alphaDummy004))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) 0)
  let alphaDummy023 : Var := (freshVar (((Class.cv alphaDummy004)).fv) 0)
  let alphaDummy024 : Var := (freshVar (((Class.cv z)).fv) 0)
  let alphaDummy025 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy026 : Var := (freshVar (((Class.cv t)).fv) 0)
  let alphaDummy027 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy028 : Var := (freshVar (((Class.cv u)).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv t))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) 0)
  let alphaDummy032 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv t)))).fv ∪ ((synCsn (synCsn (Class.cv t)))).fv) 0)
  let alphaDummy033 : Var := (freshVar (((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy034 : Var := (freshVar (((synCsn (Class.cv t))).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv ∪
        ((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy038 : Var := (freshVar (((synCpr (Class.cv t) (Class.cv u))).fv) 0)
  let alphaDummy039 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy040 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv t)))).fv ∪
        ((synCcompl (synCsn (Class.cv u)))).fv) 0)
  let alphaDummy041 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy000))).fv ∪
        ((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy042 : Var :=
    (freshVar (((synCsn (Class.cv t))).fv ∪ ((synCsn (Class.cv t))).fv) 0)
  let alphaDummy043 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy001))).fv ∪
        ((synCsn (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy044 : Var :=
    (freshVar (((synCsn (Class.cv u))).fv ∪ ((synCsn (Class.cv u))).fv) 0)
  have fresh_040 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_041 : alphaDummy001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  have fresh_042 : alphaDummy002 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 2
  have fresh_043 : alphaDummy003 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 3
  have fresh_044 : alphaDummy004 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 4
  have support_part_0000 :
    alphaDummy003 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy003))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alphaDummy003 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy003))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))))).fv)
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
    alphaDummy003 ∈ (((synCsn (synCsn (Class.cv alphaDummy003)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alphaDummy003 ∈
      (((synCsn (synCsn (Class.cv alphaDummy003)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy003)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy003)))).fv)
        support_part_0002)
  have support_part_0003 : y ∈ (((synCsn (synCsn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    y ∈ (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy003 ∈ (((synCsn (Class.cv alphaDummy003))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alphaDummy003 ∈ (((synCsn (Class.cv alphaDummy003))).fv) :=
    by exact support_part_0004
  have support_part_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by exact support_part_0005
  have support_part_0006 : alphaDummy003 ∈ (((Class.cv alphaDummy003)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alphaDummy003 ∈ (((Class.cv alphaDummy003)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by exact support_part_0007
  have support_part_0008 :
    alphaDummy003 ∈
      (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alphaDummy003 ∈
      (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv)
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
    alphaDummy003 ∈
      (((synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy003 ∈
      (((synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))).fv) :=
    by exact support_part_0010
  have support_part_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alphaDummy003 ∈ (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alphaDummy003 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy004)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv)
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
    alphaDummy003 ∈ (((synCsn (Class.cv alphaDummy003))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alphaDummy003 ∈
      (((synCsn (Class.cv alphaDummy003))).fv ∪ ((synCsn (Class.cv alphaDummy003))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy003))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    y ∈ (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy004 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alphaDummy004 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy003))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy003))))).fv)
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
    alphaDummy004 ∈
      (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alphaDummy004 ∈
      (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004)))).fv)
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
    alphaDummy004 ∈
      (((synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy004 ∈
      (((synCpr (Class.cv alphaDummy003) (Class.cv alphaDummy004))).fv) :=
    by exact support_part_0020
  have support_part_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alphaDummy004 ∈ (((synCcompl (synCsn (Class.cv alphaDummy004)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alphaDummy004 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy004)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv)
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
    alphaDummy004 ∈ (((synCsn (Class.cv alphaDummy004))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alphaDummy004 ∈
      (((synCsn (Class.cv alphaDummy004))).fv ∪ ((synCsn (Class.cv alphaDummy004))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy004))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((synCsn (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    z ∈ (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alphaDummy004 ∈ (((Class.cv alphaDummy004)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alphaDummy004 ∈ (((Class.cv alphaDummy004)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by exact support_part_0027
  have support_part_0028 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0028 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    exact support_part_0028
  have support_part_0029 : t ∈ (((Class.cv t)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0029 : t ∈ (((Class.cv t)).fv) := by exact support_part_0029
  have support_part_0030 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0030 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0030
  have support_part_0031 : u ∈ (((Class.cv u)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0031 : u ∈ (((Class.cv u)).fv) := by exact support_part_0031
  have support_part_0032 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0032 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv)
        support_part_0032)
  have support_part_0033 : t ∈ (((synCcompl (synCsn (synCsn (Class.cv t))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0033 :
    t ∈
      (((synCcompl (synCsn (synCsn (Class.cv t))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv)
        support_part_0033)
  have support_part_0034 :
    alphaDummy000 ∈ (((synCsn (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0034 :
    alphaDummy000 ∈
      (((synCsn (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
        support_part_0034)
  have support_part_0035 : t ∈ (((synCsn (synCsn (Class.cv t)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0035 :
    t ∈ (((synCsn (synCsn (Class.cv t)))).fv ∪ ((synCsn (synCsn (Class.cv t)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv t)))).fv) support_part_0035)
  have support_part_0036 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0036 : alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) :=
    by exact support_part_0036
  have support_part_0037 : t ∈ (((synCsn (Class.cv t))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0037 : t ∈ (((synCsn (Class.cv t))).fv) := by exact support_part_0037
  have support_part_0038 :
    alphaDummy000 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0038 :
    alphaDummy000 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv)
        support_part_0038)
  have support_part_0039 : t ∈ (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0039 :
    t ∈
      (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv ∪
        ((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv)
        support_part_0039)
  have support_part_0040 :
    alphaDummy000 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0040 :
    alphaDummy000 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0040
  have support_part_0041 : t ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0041 : t ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    exact support_part_0041
  have support_part_0042 :
    alphaDummy000 ∈ (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0042 :
    alphaDummy000 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv)
        support_part_0042)
  have support_part_0043 : t ∈ (((synCcompl (synCsn (Class.cv t)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0043 :
    t ∈
      (((synCcompl (synCsn (Class.cv t)))).fv ∪ ((synCcompl (synCsn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv u)))).fv) support_part_0043)
  have support_part_0044 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0044 :
    alphaDummy000 ∈
      (((synCsn (Class.cv alphaDummy000))).fv ∪ ((synCsn (Class.cv alphaDummy000))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy000))).fv) support_part_0044)
  have support_part_0045 : t ∈ (((synCsn (Class.cv t))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0045 :
    t ∈ (((synCsn (Class.cv t))).fv ∪ ((synCsn (Class.cv t))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv t))).fv) support_part_0045)
  have support_part_0046 :
    alphaDummy001 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0046 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy000))))).fv)
        support_part_0046)
  have support_part_0047 :
    u ∈ (((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0047 :
    u ∈
      (((synCcompl (synCsn (synCsn (Class.cv t))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv t) (Class.cv u))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv t))))).fv)
        support_part_0047)
  have support_part_0048 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0048 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001)))).fv)
        support_part_0048)
  have support_part_0049 : u ∈ (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0049 :
    u ∈
      (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv ∪
        ((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCpr (Class.cv t) (Class.cv u)))).fv)
        support_part_0049)
  have support_part_0050 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0050 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy000) (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0050
  have support_part_0051 : u ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0051 : u ∈ (((synCpr (Class.cv t) (Class.cv u))).fv) := by
    exact support_part_0051
  have support_part_0052 :
    alphaDummy001 ∈ (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0052 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy000)))).fv)
        support_part_0052)
  have support_part_0053 : u ∈ (((synCcompl (synCsn (Class.cv u)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0053 :
    u ∈
      (((synCcompl (synCsn (Class.cv t)))).fv ∪ ((synCcompl (synCsn (Class.cv u)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv t)))).fv) support_part_0053)
  have support_part_0054 :
    alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0054 :
    alphaDummy001 ∈
      (((synCsn (Class.cv alphaDummy001))).fv ∪ ((synCsn (Class.cv alphaDummy001))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy001))).fv) support_part_0054)
  have support_part_0055 : u ∈ (((synCsn (Class.cv u))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0055 :
    u ∈ (((synCsn (Class.cv u))).fv ∪ ((synCsn (Class.cv u))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv u))).fv) support_part_0055)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy017, alphaDummy018), (alphaDummy015, alphaDummy016),
        (alphaDummy013, alphaDummy014), (alphaDummy005, alphaDummy006),
        (alphaDummy004, z), (alphaDummy003, y), (alphaDummy002, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy017)
          (synCcompl (synCsn (Class.cv alphaDummy003)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy017)
            (synCcompl (synCsn (Class.cv alphaDummy004))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy018) (synCcompl (synCsn (Class.cv y))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy018)
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
      [(alphaDummy039, alphaDummy040), (alphaDummy037, alphaDummy038),
        (alphaDummy035, alphaDummy036), (alphaDummy029, alphaDummy030),
        (alphaDummy001, u), (alphaDummy000, t), (alphaDummy004, z),
        (alphaDummy003, y), (alphaDummy002, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy039)
          (synCcompl (synCsn (Class.cv alphaDummy000)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy039)
            (synCcompl (synCsn (Class.cv alphaDummy001))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy040) (synCcompl (synCsn (Class.cv t))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy040)
            (synCcompl (synCsn (Class.cv u)))))) :=
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
  have splitAlpha0002 :
    TAlphaWff [(alphaDummy004, z), (alphaDummy003, y), (alphaDummy002, x)]
      (Wff.imp (Wff.classEq (Class.cv alphaDummy002)
          (synCopk (Class.cv alphaDummy003) (Class.cv alphaDummy004))) (Wff.neg
          (synWex alphaDummy000 (synWex alphaDummy001 (synW3a
                (Wff.classEq (Class.cv alphaDummy003) (synCsn (Class.cv alphaDummy000)))
                (Wff.classEq (Class.cv alphaDummy004) (synCsn (Class.cv alphaDummy001)))
                (Wff.classMem
                  (synCopk (Class.cv alphaDummy000) (Class.cv alphaDummy001)) A))))))
      (Wff.imp (Wff.classEq (Class.cv x) (synCopk (Class.cv y) (Class.cv z))) (Wff.neg
          (synWex t (synWex u (synW3a (Wff.classEq (Class.cv y) (synCsn (Class.cv t)))
                (Wff.classEq (Class.cv z) (synCsn (Class.cv u)))
                (Wff.classMem (synCopk (Class.cv t) (Class.cv u)) A)))))) :=
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
                              (TAlphaWff.neg (TAlphaWff.neg splitAlpha0000))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg splitAlpha0000))))))))))))))
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
                                      (TAlphaWff.neg (TAlphaWff.neg splitAlpha0001))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.classEq
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg splitAlpha0001)))))))))))))
                (TAlphaClass.reflOfFvFresh _ _ (by
                    intro a b h hne;
                    simp only [List.mem_cons, List.not_mem_nil, or_false,
                      Prod.mk.injEq] at h;
                    repeat'
                      (first
                        | (rcases h with ⟨rfl, rfl⟩));
                      all_goals aesop))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg splitAlpha0002))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
