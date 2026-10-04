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

/-- Checked nominal proof certificate identified upstream as `nominal_df_p6`. -/
@[expose]
noncomputable def nominalDfP6 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.classEq (synCp6 A)
        (.cab x (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv x)))) A))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var :=
    (freshVar (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))
            A)).fv ∪
        ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv)
      0)
  let alphaDummy002 : Var :=
    (freshVar (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv ∪
        ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar
      (((synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ (A).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((synCxpk (synCvv) (synCsn (synCsn (Class.cv x))))).fv ∪ (A).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) 1)
  let alphaDummy007 : Var :=
    (freshVar (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) 2)
  let alphaDummy008 : Var :=
    (freshVar (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 0)
  let alphaDummy009 : Var :=
    (freshVar (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 1)
  let alphaDummy010 : Var :=
    (freshVar (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) 2)
  let alphaDummy011 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy006))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))))).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy009))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))))).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy006)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy006)))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy009)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy009)))).fv) 0)
  let alphaDummy015 : Var := (freshVar (((synCsn (Class.cv alphaDummy006))).fv) 0)
  let alphaDummy016 : Var := (freshVar (((synCsn (Class.cv alphaDummy009))).fv) 0)
  let alphaDummy017 : Var := (freshVar (((Class.cv alphaDummy006)).fv) 0)
  let alphaDummy018 : Var := (freshVar (((Class.cv alphaDummy009)).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy006)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy007)))).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy009)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy010)))).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy006))).fv ∪
        ((synCsn (Class.cv alphaDummy006))).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy009))).fv ∪
        ((synCsn (Class.cv alphaDummy009))).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy007))).fv ∪
        ((synCsn (Class.cv alphaDummy007))).fv) 0)
  let alphaDummy028 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy010))).fv ∪
        ((synCsn (Class.cv alphaDummy010))).fv) 0)
  let alphaDummy029 : Var := (freshVar (((Class.cv alphaDummy007)).fv) 0)
  let alphaDummy030 : Var := (freshVar (((Class.cv alphaDummy010)).fv) 0)
  let alphaDummy031 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy032 : Var := (freshVar (((synCsn (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy033 : Var := (freshVar (((synCsn (Class.cv x))).fv) 0)
  let alphaDummy034 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy035 : Var := (freshVar (((Class.cv x)).fv) 0)
  have fresh_010 :
    alphaDummy001 ∉
      (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv ∪
        ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))
            A)).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv ∪
          ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv)
        0
  have fresh_011 :
    alphaDummy002 ∉
      (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv ∪
        ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv ∪
          ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv)
        0
  have fresh_038 :
    alphaDummy003 ∉
      (((synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ (A).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ (A).fv)
        0
  have fresh_039 :
    alphaDummy004 ∉
      (((synCxpk (synCvv) (synCsn (synCsn (Class.cv x))))).fv ∪ (A).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCxpk (synCvv) (synCsn (synCsn (Class.cv x))))).fv ∪ (A).fv) 0
  have fresh_040 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have support_part_0000 :
    alphaDummy006 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy006))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alphaDummy006 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy006))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))))).fv)
        support_part_0000)
  have support_part_0001 :
    alphaDummy009 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy009))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0001 :
    alphaDummy009 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy009))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))))).fv)
        support_part_0001)
  have support_part_0002 :
    alphaDummy006 ∈ (((synCsn (synCsn (Class.cv alphaDummy006)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alphaDummy006 ∈
      (((synCsn (synCsn (Class.cv alphaDummy006)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy006)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy006)))).fv)
        support_part_0002)
  have support_part_0003 :
    alphaDummy009 ∈ (((synCsn (synCsn (Class.cv alphaDummy009)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    alphaDummy009 ∈
      (((synCsn (synCsn (Class.cv alphaDummy009)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy009)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy009)))).fv)
        support_part_0003)
  have support_part_0004 :
    alphaDummy006 ∈ (((synCsn (Class.cv alphaDummy006))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alphaDummy006 ∈ (((synCsn (Class.cv alphaDummy006))).fv) :=
    by exact support_part_0004
  have support_part_0005 :
    alphaDummy009 ∈ (((synCsn (Class.cv alphaDummy009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : alphaDummy009 ∈ (((synCsn (Class.cv alphaDummy009))).fv) :=
    by exact support_part_0005
  have support_part_0006 : alphaDummy006 ∈ (((Class.cv alphaDummy006)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alphaDummy006 ∈ (((Class.cv alphaDummy006)).fv) := by
    exact support_part_0006
  have support_part_0007 : alphaDummy009 ∈ (((Class.cv alphaDummy009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : alphaDummy009 ∈ (((Class.cv alphaDummy009)).fv) := by
    exact support_part_0007
  have support_part_0008 :
    alphaDummy006 ∈
      (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alphaDummy006 ∈
      (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv)
        support_part_0008)
  have support_part_0009 :
    alphaDummy009 ∈
      (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0009 :
    alphaDummy009 ∈
      (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv)
        support_part_0009)
  have support_part_0010 :
    alphaDummy006 ∈
      (((synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy006 ∈
      (((synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))).fv) :=
    by exact support_part_0010
  have support_part_0011 :
    alphaDummy009 ∈
      (((synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 :
    alphaDummy009 ∈
      (((synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by exact support_part_0011
  have support_part_0012 :
    alphaDummy006 ∈ (((synCcompl (synCsn (Class.cv alphaDummy006)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alphaDummy006 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy006)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy007)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy007)))).fv)
        support_part_0012)
  have support_part_0013 :
    alphaDummy009 ∈ (((synCcompl (synCsn (Class.cv alphaDummy009)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0013 :
    alphaDummy009 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy009)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy010)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy010)))).fv)
        support_part_0013)
  have support_part_0014 :
    alphaDummy006 ∈ (((synCsn (Class.cv alphaDummy006))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alphaDummy006 ∈
      (((synCsn (Class.cv alphaDummy006))).fv ∪ ((synCsn (Class.cv alphaDummy006))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy006))).fv) support_part_0014)
  have support_part_0015 :
    alphaDummy009 ∈ (((synCsn (Class.cv alphaDummy009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    alphaDummy009 ∈
      (((synCsn (Class.cv alphaDummy009))).fv ∪ ((synCsn (Class.cv alphaDummy009))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy009))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy007 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alphaDummy007 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy006))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy006))))).fv)
        support_part_0016)
  have support_part_0017 :
    alphaDummy010 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0017 :
    alphaDummy010 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy009))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy009))))).fv)
        support_part_0017)
  have support_part_0018 :
    alphaDummy007 ∈
      (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alphaDummy007 ∈
      (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007)))).fv)
        support_part_0018)
  have support_part_0019 :
    alphaDummy010 ∈
      (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0019 :
    alphaDummy010 ∈
      (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010)))).fv)
        support_part_0019)
  have support_part_0020 :
    alphaDummy007 ∈
      (((synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy007 ∈
      (((synCpr (Class.cv alphaDummy006) (Class.cv alphaDummy007))).fv) :=
    by exact support_part_0020
  have support_part_0021 :
    alphaDummy010 ∈
      (((synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 :
    alphaDummy010 ∈
      (((synCpr (Class.cv alphaDummy009) (Class.cv alphaDummy010))).fv) :=
    by exact support_part_0021
  have support_part_0022 :
    alphaDummy007 ∈ (((synCcompl (synCsn (Class.cv alphaDummy007)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alphaDummy007 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy006)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy007)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy006)))).fv)
        support_part_0022)
  have support_part_0023 :
    alphaDummy010 ∈ (((synCcompl (synCsn (Class.cv alphaDummy010)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0023 :
    alphaDummy010 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy009)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy010)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy009)))).fv)
        support_part_0023)
  have support_part_0024 :
    alphaDummy007 ∈ (((synCsn (Class.cv alphaDummy007))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alphaDummy007 ∈
      (((synCsn (Class.cv alphaDummy007))).fv ∪ ((synCsn (Class.cv alphaDummy007))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy007))).fv) support_part_0024)
  have support_part_0025 :
    alphaDummy010 ∈ (((synCsn (Class.cv alphaDummy010))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    alphaDummy010 ∈
      (((synCsn (Class.cv alphaDummy010))).fv ∪ ((synCsn (Class.cv alphaDummy010))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy010))).fv) support_part_0025)
  have support_part_0026 : alphaDummy007 ∈ (((Class.cv alphaDummy007)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alphaDummy007 ∈ (((Class.cv alphaDummy007)).fv) := by
    exact support_part_0026
  have support_part_0027 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) := by
    exact support_part_0027
  have support_part_0028 :
    alphaDummy000 ∈
      (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin,
      fv_syn_csn, fv_syn_cvv, fv_syn_cxpk, eq_self, true_or, or_true]
  have support_mem_0028 :
    alphaDummy000 ∈
      (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv ∪
        ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))
            A)).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000)))) A)).fv)
        support_part_0028)
  have support_part_0029 :
    x ∈ (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin,
      fv_syn_csn, fv_syn_cvv, fv_syn_cxpk, eq_self, true_or, or_true]
  have support_mem_0029 :
    x ∈
      (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv ∪
        ((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (synCxpk (synCvv) (synCsn (synCsn (Class.cv x)))) A)).fv)
        support_part_0029)
  have support_part_0030 :
    alphaDummy000 ∈
      (((synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn,
      fv_syn_cvv, fv_syn_cxpk, eq_self, or_true]
  have support_mem_0030 :
    alphaDummy000 ∈
      (((synCxpk (synCvv) (synCsn (synCsn (Class.cv alphaDummy000))))).fv ∪ (A).fv) :=
    by exact (Finset.mem_union_left ((A).fv) support_part_0030)
  have support_part_0031 :
    x ∈ (((synCxpk (synCvv) (synCsn (synCsn (Class.cv x))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_csn,
      fv_syn_cvv, fv_syn_cxpk, eq_self, or_true]
  have support_mem_0031 :
    x ∈ (((synCxpk (synCvv) (synCsn (synCsn (Class.cv x))))).fv ∪ (A).fv) := by
    exact (Finset.mem_union_left ((A).fv) support_part_0031)
  have support_part_0032 :
    alphaDummy000 ∈ (((synCsn (synCsn (Class.cv alphaDummy000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0032 :
    alphaDummy000 ∈
      (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) :=
    by exact (Finset.mem_union_right (((synCvv)).fv) support_part_0032)
  have support_part_0033 : x ∈ (((synCsn (synCsn (Class.cv x)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0033 : x ∈ (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) :=
    by exact (Finset.mem_union_right (((synCvv)).fv) support_part_0033)
  have support_part_0034 :
    alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0034 : alphaDummy000 ∈ (((synCsn (Class.cv alphaDummy000))).fv) :=
    by exact support_part_0034
  have support_part_0035 : x ∈ (((synCsn (Class.cv x))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0035 : x ∈ (((synCsn (Class.cv x))).fv) := by exact support_part_0035
  have support_part_0036 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0036 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    exact support_part_0036
  have support_part_0037 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0037 : x ∈ (((Class.cv x)).fv) := by exact support_part_0037
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy023, alphaDummy024), (alphaDummy021, alphaDummy022),
        (alphaDummy019, alphaDummy020), (alphaDummy011, alphaDummy012),
        (alphaDummy007, alphaDummy010), (alphaDummy006, alphaDummy009),
        (alphaDummy005, alphaDummy008), (alphaDummy003, alphaDummy004),
        (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy023)
          (synCcompl (synCsn (Class.cv alphaDummy006)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy023)
            (synCcompl (synCsn (Class.cv alphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy024)
          (synCcompl (synCsn (Class.cv alphaDummy009)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy024)
            (synCcompl (synCsn (Class.cv alphaDummy010)))))) :=
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
                                  (TAlphaVar.there (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                                      (by decide)) (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv x)))).fv) (by decide))
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
                                  (TAlphaVar.there (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                                      (by decide)) (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv x)))).fv) (by decide))
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
      [(alphaDummy007, alphaDummy010), (alphaDummy006, alphaDummy009),
        (alphaDummy005, alphaDummy008), (alphaDummy003, alphaDummy004),
        (alphaDummy001, alphaDummy002), (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (Class.cv alphaDummy005)
          (synCopk (Class.cv alphaDummy006) (Class.cv alphaDummy007))) (Wff.neg
          (synWa (Wff.classMem (Class.cv alphaDummy006) (synCvv))
            (Wff.classMem (Class.cv alphaDummy007)
              (synCsn (synCsn (Class.cv alphaDummy000)))))))
      (Wff.imp (Wff.classEq (Class.cv alphaDummy008)
          (synCopk (Class.cv alphaDummy009) (Class.cv alphaDummy010))) (Wff.neg
          (synWa (Wff.classMem (Class.cv alphaDummy009) (synCvv))
            (Wff.classMem (Class.cv alphaDummy010) (synCsn (synCsn (Class.cv x))))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
              (by decide))
            (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                (by decide))
              (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
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
        (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) (by decide))
        (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
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
        (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) (by decide))
        (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
        (by decide)) (TAlphaVar.here _ _ _))))))))))))))))
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
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective
                  (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                  (by decide)) (freshVar_injective
                  (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) (by decide))
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
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy023, alphaDummy024), (alphaDummy021, alphaDummy022),
        (alphaDummy019, alphaDummy020), (alphaDummy011, alphaDummy012),
        (alphaDummy007, alphaDummy010), (alphaDummy006, alphaDummy009),
        (alphaDummy005, alphaDummy008), (alphaDummy000, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy023)
          (synCcompl (synCsn (Class.cv alphaDummy006)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy023)
            (synCcompl (synCsn (Class.cv alphaDummy007))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy024)
          (synCcompl (synCsn (Class.cv alphaDummy009)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy024)
            (synCcompl (synCsn (Class.cv alphaDummy010)))))) :=
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
                                  (TAlphaVar.there (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                                      (by decide)) (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv x)))).fv) (by decide))
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
                                  (TAlphaVar.there (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                                      (by decide)) (freshVar_injective (((synCvv)).fv ∪
                                        ((synCsn (synCsn (Class.cv x)))).fv) (by decide))
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
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy007, alphaDummy010), (alphaDummy006, alphaDummy009),
        (alphaDummy005, alphaDummy008), (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (Class.cv alphaDummy005)
          (synCopk (Class.cv alphaDummy006) (Class.cv alphaDummy007))) (Wff.neg
          (synWa (Wff.classMem (Class.cv alphaDummy006) (synCvv))
            (Wff.classMem (Class.cv alphaDummy007)
              (synCsn (synCsn (Class.cv alphaDummy000)))))))
      (Wff.imp (Wff.classEq (Class.cv alphaDummy008)
          (synCopk (Class.cv alphaDummy009) (Class.cv alphaDummy010))) (Wff.neg
          (synWa (Wff.classMem (Class.cv alphaDummy009) (synCvv))
            (Wff.classMem (Class.cv alphaDummy010) (synCsn (synCsn (Class.cv x))))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
              (by decide))
            (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
              (by decide)) (TAlphaVar.there (freshVar_injective
                (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                (by decide))
              (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
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
        (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) (by decide))
        (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
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
        (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv) (by decide))
        (freshVar_injective (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv)
        (by decide)) (TAlphaVar.here _ _ _))))))))))))))))
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
                            (TAlphaClass.cab
                              (TAlphaWff.neg (TAlphaWff.neg splitAlpha0002))))))))))))))
      (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective
                  (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv alphaDummy000)))).fv)
                  (by decide)) (freshVar_injective
                  (((synCvv)).fv ∪ ((synCsn (synCsn (Class.cv x)))).fv) (by decide))
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
                              (TAlphaWff.ex (TAlphaWff.neg splitAlpha0001)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfFvFresh _ _ (by
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
                              (TAlphaWff.ex (TAlphaWff.neg splitAlpha0001)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfFvFresh _ _ (by
                              intro a b h hne;
                              simp only [List.mem_cons, List.not_mem_nil, or_false,
                                Prod.mk.injEq] at h;
                              repeat'
                                (first
                                  | (rcases h with ⟨rfl, rfl⟩));
                                all_goals aesop)))))))))) (TAlphaClass.cab
            (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg splitAlpha0003))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
