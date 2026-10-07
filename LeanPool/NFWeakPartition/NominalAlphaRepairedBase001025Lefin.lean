/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001025Lefin. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_lefin`. -/
@[expose]
noncomputable def nominalDfLefin (x : Var) (y : Var) (z : Var) (w : Var)
    (__dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synClefin) (.cab x (synWex y (synWex z
              (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWrex w (synCnnc)
                  (.classEq (.cv z) (synCplc (.cv y) (.cv w))))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy002 : Var := (freshVar ((∅ : Finset Var)) 2)
  let alphaDummy003 : Var := (freshVar ((∅ : Finset Var)) 3)
  let alphaDummy004 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy002))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))))).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv y))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy002)))).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) 0)
  let alphaDummy008 : Var := (freshVar (((synCsn (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy009 : Var := (freshVar (((synCsn (Class.cv y))).fv) 0)
  let alphaDummy010 : Var := (freshVar (((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy011 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv ∪
        ((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))).fv) 0)
  let alphaDummy015 : Var := (freshVar (((synCpr (Class.cv y) (Class.cv z))).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy003)))).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv y)))).fv ∪
        ((synCcompl (synCsn (Class.cv z)))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy002))).fv ∪
        ((synCsn (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy003))).fv ∪
        ((synCsn (Class.cv alphaDummy003))).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) 0)
  let alphaDummy022 : Var := (freshVar (((Class.cv alphaDummy003)).fv) 0)
  let alphaDummy023 : Var := (freshVar (((Class.cv z)).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 1)
  let alphaDummy026 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy028 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy029 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy031 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy032 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy033 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy034 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv ∪
        ((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy032)).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy031))).fv ∪
        ((synCcompl (Class.cv alphaDummy032))).fv) 0)
  let alphaDummy037 : Var :=
    (freshVar (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy031)).fv) 0)
  let alphaDummy038 : Var :=
    (freshVar (((Class.cv alphaDummy032)).fv ∪ ((Class.cv alphaDummy032)).fv) 0)
  let alphaDummy039 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy040 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv) 1)
  let alphaDummy041 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv) 2)
  let alphaDummy042 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 0)
  let alphaDummy043 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 1)
  let alphaDummy044 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv w)).fv) 2)
  let alphaDummy045 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv ∪
        ((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv) 0)
  let alphaDummy046 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv ∪
        ((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv) 0)
  let alphaDummy047 : Var :=
    (freshVar (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy041)).fv) 0)
  let alphaDummy048 : Var :=
    (freshVar (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy044)).fv) 0)
  let alphaDummy049 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy040))).fv ∪
        ((synCcompl (Class.cv alphaDummy041))).fv) 0)
  let alphaDummy050 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy043))).fv ∪
        ((synCcompl (Class.cv alphaDummy044))).fv) 0)
  let alphaDummy051 : Var :=
    (freshVar (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy040)).fv) 0)
  let alphaDummy052 : Var :=
    (freshVar (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy043)).fv) 0)
  let alphaDummy053 : Var :=
    (freshVar (((Class.cv alphaDummy041)).fv ∪ ((Class.cv alphaDummy041)).fv) 0)
  let alphaDummy054 : Var :=
    (freshVar (((Class.cv alphaDummy044)).fv ∪ ((Class.cv alphaDummy044)).fv) 0)
  have support_part_0000 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy002))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy002))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))))).fv)
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
    alphaDummy002 ∈ (((synCsn (synCsn (Class.cv alphaDummy002)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alphaDummy002 ∈
      (((synCsn (synCsn (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy002)))).fv)
        support_part_0002)
  have support_part_0003 : y ∈ (((synCsn (synCsn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    y ∈ (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy002 ∈ (((synCsn (Class.cv alphaDummy002))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alphaDummy002 ∈ (((synCsn (Class.cv alphaDummy002))).fv) :=
    by exact support_part_0004
  have support_part_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by exact support_part_0005
  have support_part_0006 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by exact support_part_0007
  have support_part_0008 :
    alphaDummy002 ∈
      (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alphaDummy002 ∈
      (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv)
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
    alphaDummy002 ∈
      (((synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy002 ∈
      (((synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))).fv) :=
    by exact support_part_0010
  have support_part_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alphaDummy002 ∈ (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy003)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv)
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
    alphaDummy002 ∈ (((synCsn (Class.cv alphaDummy002))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alphaDummy002 ∈
      (((synCsn (Class.cv alphaDummy002))).fv ∪ ((synCsn (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy002))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    y ∈ (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy003 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alphaDummy003 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy002))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy002))))).fv)
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
    alphaDummy003 ∈
      (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alphaDummy003 ∈
      (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003)))).fv)
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
    alphaDummy003 ∈
      (((synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy003 ∈
      (((synCpr (Class.cv alphaDummy002) (Class.cv alphaDummy003))).fv) :=
    by exact support_part_0020
  have support_part_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alphaDummy003 ∈ (((synCcompl (synCsn (Class.cv alphaDummy003)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alphaDummy003 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy003)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv)
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
    alphaDummy003 ∈ (((synCsn (Class.cv alphaDummy003))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alphaDummy003 ∈
      (((synCsn (Class.cv alphaDummy003))).fv ∪ ((synCsn (Class.cv alphaDummy003))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy003))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((synCsn (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    z ∈ (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alphaDummy003 ∈ (((Class.cv alphaDummy003)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alphaDummy003 ∈ (((Class.cv alphaDummy003)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by exact support_part_0027
  have support_part_0028 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0028 :
    alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0028)
  have support_part_0029 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0029 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0029
  have support_part_0030 :
    alphaDummy031 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0030 :
    alphaDummy031 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv ∪
        ((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv)
        support_part_0030)
  have support_part_0031 : alphaDummy031 ∈ (((Class.cv alphaDummy031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0031 :
    alphaDummy031 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy032)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy032)).fv) support_part_0031)
  have support_part_0032 :
    alphaDummy032 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0032 :
    alphaDummy032 ∈
      (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv ∪
        ((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy031) (Class.cv alphaDummy032))).fv)
        support_part_0032)
  have support_part_0033 : alphaDummy032 ∈ (((Class.cv alphaDummy032)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0033 :
    alphaDummy032 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy032)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy031)).fv) support_part_0033)
  have support_part_0034 :
    alphaDummy031 ∈ (((synCcompl (Class.cv alphaDummy031))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0034 :
    alphaDummy031 ∈
      (((synCcompl (Class.cv alphaDummy031))).fv ∪
        ((synCcompl (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy032))).fv) support_part_0034)
  have support_part_0035 : alphaDummy031 ∈ (((Class.cv alphaDummy031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0035 :
    alphaDummy031 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy031)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy031)).fv) support_part_0035)
  have support_part_0036 :
    alphaDummy032 ∈ (((synCcompl (Class.cv alphaDummy032))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0036 :
    alphaDummy032 ∈
      (((synCcompl (Class.cv alphaDummy031))).fv ∪
        ((synCcompl (Class.cv alphaDummy032))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy031))).fv) support_part_0036)
  have support_part_0037 : alphaDummy032 ∈ (((Class.cv alphaDummy032)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0037 :
    alphaDummy032 ∈
      (((Class.cv alphaDummy032)).fv ∪ ((Class.cv alphaDummy032)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy032)).fv) support_part_0037)
  have support_part_0038 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0038 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy000)).fv) support_part_0038)
  have support_part_0039 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0039 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    exact (Finset.mem_union_left (((Class.cv w)).fv) support_part_0039)
  have support_part_0040 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0040 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy002)).fv) support_part_0040)
  have support_part_0041 : w ∈ (((Class.cv w)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0041 : w ∈ (((Class.cv y)).fv ∪ ((Class.cv w)).fv) := by
    exact (Finset.mem_union_right (((Class.cv y)).fv) support_part_0041)
  have support_part_0042 :
    alphaDummy040 ∈
      (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0042 :
    alphaDummy040 ∈
      (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv ∪
        ((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv)
        support_part_0042)
  have support_part_0043 :
    alphaDummy043 ∈
      (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0043 :
    alphaDummy043 ∈
      (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv ∪
        ((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv)
        support_part_0043)
  have support_part_0044 : alphaDummy040 ∈ (((Class.cv alphaDummy040)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0044 :
    alphaDummy040 ∈
      (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy041)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy041)).fv) support_part_0044)
  have support_part_0045 : alphaDummy043 ∈ (((Class.cv alphaDummy043)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0045 :
    alphaDummy043 ∈
      (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy044)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy044)).fv) support_part_0045)
  have support_part_0046 :
    alphaDummy041 ∈
      (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0046 :
    alphaDummy041 ∈
      (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv ∪
        ((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy040) (Class.cv alphaDummy041))).fv)
        support_part_0046)
  have support_part_0047 :
    alphaDummy044 ∈
      (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0047 :
    alphaDummy044 ∈
      (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv ∪
        ((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy043) (Class.cv alphaDummy044))).fv)
        support_part_0047)
  have support_part_0048 : alphaDummy041 ∈ (((Class.cv alphaDummy041)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0048 :
    alphaDummy041 ∈
      (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy041)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy040)).fv) support_part_0048)
  have support_part_0049 : alphaDummy044 ∈ (((Class.cv alphaDummy044)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0049 :
    alphaDummy044 ∈
      (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy044)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy043)).fv) support_part_0049)
  have support_part_0050 :
    alphaDummy040 ∈ (((synCcompl (Class.cv alphaDummy040))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0050 :
    alphaDummy040 ∈
      (((synCcompl (Class.cv alphaDummy040))).fv ∪
        ((synCcompl (Class.cv alphaDummy041))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy041))).fv) support_part_0050)
  have support_part_0051 :
    alphaDummy043 ∈ (((synCcompl (Class.cv alphaDummy043))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0051 :
    alphaDummy043 ∈
      (((synCcompl (Class.cv alphaDummy043))).fv ∪
        ((synCcompl (Class.cv alphaDummy044))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy044))).fv) support_part_0051)
  have support_part_0052 : alphaDummy040 ∈ (((Class.cv alphaDummy040)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0052 :
    alphaDummy040 ∈
      (((Class.cv alphaDummy040)).fv ∪ ((Class.cv alphaDummy040)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy040)).fv) support_part_0052)
  have support_part_0053 : alphaDummy043 ∈ (((Class.cv alphaDummy043)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0053 :
    alphaDummy043 ∈
      (((Class.cv alphaDummy043)).fv ∪ ((Class.cv alphaDummy043)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy043)).fv) support_part_0053)
  have support_part_0054 :
    alphaDummy041 ∈ (((synCcompl (Class.cv alphaDummy041))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0054 :
    alphaDummy041 ∈
      (((synCcompl (Class.cv alphaDummy040))).fv ∪
        ((synCcompl (Class.cv alphaDummy041))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy040))).fv) support_part_0054)
  have support_part_0055 :
    alphaDummy044 ∈ (((synCcompl (Class.cv alphaDummy044))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0055 :
    alphaDummy044 ∈
      (((synCcompl (Class.cv alphaDummy043))).fv ∪
        ((synCcompl (Class.cv alphaDummy044))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy043))).fv) support_part_0055)
  have support_part_0056 : alphaDummy041 ∈ (((Class.cv alphaDummy041)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0056 :
    alphaDummy041 ∈
      (((Class.cv alphaDummy041)).fv ∪ ((Class.cv alphaDummy041)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy041)).fv) support_part_0056)
  have support_part_0057 : alphaDummy044 ∈ (((Class.cv alphaDummy044)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0057 :
    alphaDummy044 ∈
      (((Class.cv alphaDummy044)).fv ∪ ((Class.cv alphaDummy044)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy044)).fv) support_part_0057)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy016, alphaDummy017), (alphaDummy014, alphaDummy015),
        (alphaDummy012, alphaDummy013), (alphaDummy004, alphaDummy005),
        (alphaDummy003, z), (alphaDummy002, y), (alphaDummy001, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy016)
          (synCcompl (synCsn (Class.cv alphaDummy002)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy016)
            (synCcompl (synCsn (Class.cv alphaDummy003))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy017) (synCcompl (synCsn (Class.cv y))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy017)
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
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _))))))))))))
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
                                    (freshVar_injective ((∅ : Finset Var)) (by decide))
                                    dv_y_z (TAlphaVar.here _ _ _)))))))))))))))) (TAlphaWff.neg
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
      [(alphaDummy032, alphaDummy032), (alphaDummy031, alphaDummy031),
        (alphaDummy030, alphaDummy030), (alphaDummy001, alphaDummy001),
        (alphaDummy000, alphaDummy000), (alphaDummy025, alphaDummy025),
        (alphaDummy024, alphaDummy024), (alphaDummy000, w), (alphaDummy003, z),
        (alphaDummy002, y), (alphaDummy001, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy031) (Class.cv alphaDummy032))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy030)
            (synCun (Class.cv alphaDummy031) (Class.cv alphaDummy032)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy031) (Class.cv alphaDummy032))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy030)
            (synCun (Class.cv alphaDummy031) (Class.cv alphaDummy032))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0031 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0030 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0033 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0032 0))
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
              (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0035 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0034 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0037 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0036 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy041, alphaDummy044), (alphaDummy040, alphaDummy043),
        (alphaDummy039, alphaDummy042), (alphaDummy000, w), (alphaDummy003, z),
        (alphaDummy002, y), (alphaDummy001, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy040) (Class.cv alphaDummy041))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy039)
            (synCun (Class.cv alphaDummy040) (Class.cv alphaDummy041)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy043) (Class.cv alphaDummy044))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy042)
            (synCun (Class.cv alphaDummy043) (Class.cv alphaDummy044))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy002)).fv ∪
                                    ((Class.cv alphaDummy000)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0044 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0045 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0042 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0043 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy002)).fv ∪
                                    ((Class.cv alphaDummy000)).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide))
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0048 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0049 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0046 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0047 0))
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
        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv) (by decide))
              (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide))
              (TAlphaVar.there (freshVar_injective
                  (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy000)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy002)).fv ∪
                                      ((Class.cv alphaDummy000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0052 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0053 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0050 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0051 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy002)).fv ∪
                                      ((Class.cv alphaDummy000)).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv y)).fv ∪ ((Class.cv w)).fv) (by decide))
                                  (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0056 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0057 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0054 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0055 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0003 :
    TAlphaWff
      [(alphaDummy000, w), (alphaDummy003, z), (alphaDummy002, y),
        (alphaDummy001, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy000) (synCnnc)) (Wff.neg
          (Wff.classEq (Class.cv alphaDummy003)
            (synCplc (Class.cv alphaDummy002) (Class.cv alphaDummy000)))))
      (Wff.imp (Wff.classMem (Class.cv w) (synCnnc))
        (Wff.neg (Wff.classEq (Class.cv z) (synCplc (Class.cv y) (Class.cv w))))) :=
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
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0028 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0028 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0029 0)) (TAlphaVar.here _ _ _)))))))))
                                    (TAlphaWff.neg splitAlpha0001)))))) (TAlphaClass.cv
                            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                  (freshVar_injective (((Class.cab alphaDummy000
                        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                          (synWral alphaDummy001 (Class.cv alphaDummy000)
                            (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                              (Class.cv alphaDummy000)))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alphaDummy000
                        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                          (synWral alphaDummy001 (Class.cv alphaDummy000)
                            (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                              (Class.cv alphaDummy000)))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg
        (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
              (Ne.symm dv_w_z) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 1))
                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 1))
                      (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0038 0))
                        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0039 0)) (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide)) (Ne.symm dv_w_y)
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
                            (TAlphaVar.here _ _ _))))))) (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 2))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 2)) (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 1))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 1)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0040 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0041 0))
                              (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.neg splitAlpha0002)))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_x_z
                    (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                      dv_x_y (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
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
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
        (TAlphaVar.here _ _ _))))))))))))
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
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.there
        (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_y_z
        (TAlphaVar.here _ _ _))))))))))))))))
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
              (TAlphaWff.ex (TAlphaWff.neg splitAlpha0003))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
