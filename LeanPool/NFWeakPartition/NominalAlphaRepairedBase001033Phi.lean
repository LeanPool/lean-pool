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

/-- Checked nominal proof certificate identified upstream as `nominal_df_phi`. -/
@[expose]
noncomputable def nominalDfPhi (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCphi A) (.cab y (synWrex x A (.classEq (.cv y)
              (synCif (.classMem (.cv x) (synCnnc)) (synCplc (.cv x) (synC1c))
                (.cv x)))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv) 1)
  let alphaDummy002 : Var :=
    (freshVar (((Wff.classMem (Class.cv alphaDummy000) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy000) (synC1c))).fv ∪
        ((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((Wff.classMem (Class.cv x) (synCnnc))).fv ∪
          ((synCplc (Class.cv x) (synC1c))).fv ∪ ((Class.cv x)).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy006 : Var :=
    (freshVar (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy007 : Var := (freshVar (((Class.cv x)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy008 : Var := (freshVar (((Class.cv x)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy009 : Var := (freshVar (((Class.cv x)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy010 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy011 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy012 : Var := (freshVar (((Class.cv alphaDummy011)).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv ∪
        ((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv ∪
        ((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy005)).fv ∪ ((Class.cv alphaDummy006)).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy009)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy018 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy019 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy005))).fv ∪
        ((synCcompl (Class.cv alphaDummy006))).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy008))).fv ∪
        ((synCcompl (Class.cv alphaDummy009))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((Class.cv alphaDummy005)).fv ∪ ((Class.cv alphaDummy005)).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy008)).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy006)).fv ∪ ((Class.cv alphaDummy006)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy009)).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cab alphaDummy010
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy010))
            (synWral alphaDummy011 (Class.cv alphaDummy010)
              (Wff.classMem (synCplc (Class.cv alphaDummy011) (synC1c))
                (Class.cv alphaDummy010)))))).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((Class.cab alphaDummy010
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy010))
            (synWral alphaDummy011 (Class.cv alphaDummy010)
              (Wff.classMem (synCplc (Class.cv alphaDummy011) (synC1c))
                (Class.cv alphaDummy010)))))).fv) 1)
  let alphaDummy028 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy029 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy030 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy031 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy032 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv ∪
        ((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv) 0)
  let alphaDummy033 : Var :=
    (freshVar (((Class.cv alphaDummy030)).fv ∪ ((Class.cv alphaDummy031)).fv) 0)
  let alphaDummy034 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy030))).fv ∪
        ((synCcompl (Class.cv alphaDummy031))).fv) 0)
  let alphaDummy035 : Var :=
    (freshVar (((Class.cv alphaDummy030)).fv ∪ ((Class.cv alphaDummy030)).fv) 0)
  let alphaDummy036 : Var :=
    (freshVar (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy031)).fv) 0)
  have fresh_043 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_044 : alphaDummy001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  have support_part_0000 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alphaDummy000 ∈
      (((Wff.classMem (Class.cv alphaDummy000) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy000) (synC1c))).fv ∪
        ((Class.cv alphaDummy000)).fv) :=
    by
    exact
      (Finset.mem_union_right (((Wff.classMem (Class.cv alphaDummy000) (synCnnc))).fv ∪
          ((synCplc (Class.cv alphaDummy000) (synC1c))).fv) support_part_0000)
  have support_part_0001 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 :
    x ∈
      (((Wff.classMem (Class.cv x) (synCnnc))).fv ∪ ((synCplc (Class.cv x) (synC1c))).fv ∪
        ((Class.cv x)).fv) :=
    by
    exact
      (Finset.mem_union_right (((Wff.classMem (Class.cv x) (synCnnc))).fv ∪
          ((synCplc (Class.cv x) (synC1c))).fv) support_part_0001)
  have support_part_0002 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 :
    alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0002)
  have support_part_0003 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 : x ∈ (((Class.cv x)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0003)
  have support_part_0004 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0004 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    exact support_part_0004
  have support_part_0005 :
    alphaDummy005 ∈
      (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0005 :
    alphaDummy005 ∈
      (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv ∪
        ((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv)
        support_part_0005)
  have support_part_0006 :
    alphaDummy008 ∈
      (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0006 :
    alphaDummy008 ∈
      (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv ∪
        ((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv)
        support_part_0006)
  have support_part_0007 : alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alphaDummy005 ∈
      (((Class.cv alphaDummy005)).fv ∪ ((Class.cv alphaDummy006)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy006)).fv) support_part_0007)
  have support_part_0008 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0008 :
    alphaDummy008 ∈
      (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy009)).fv) support_part_0008)
  have support_part_0009 :
    alphaDummy006 ∈
      (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0009 :
    alphaDummy006 ∈
      (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv ∪
        ((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy005) (Class.cv alphaDummy006))).fv)
        support_part_0009)
  have support_part_0010 :
    alphaDummy009 ∈
      (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0010 :
    alphaDummy009 ∈
      (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv ∪
        ((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy008) (Class.cv alphaDummy009))).fv)
        support_part_0010)
  have support_part_0011 : alphaDummy006 ∈ (((Class.cv alphaDummy006)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0011 :
    alphaDummy006 ∈
      (((Class.cv alphaDummy005)).fv ∪ ((Class.cv alphaDummy006)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy005)).fv) support_part_0011)
  have support_part_0012 : alphaDummy009 ∈ (((Class.cv alphaDummy009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0012 :
    alphaDummy009 ∈
      (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy008)).fv) support_part_0012)
  have support_part_0013 :
    alphaDummy005 ∈ (((synCcompl (Class.cv alphaDummy005))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0013 :
    alphaDummy005 ∈
      (((synCcompl (Class.cv alphaDummy005))).fv ∪
        ((synCcompl (Class.cv alphaDummy006))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy006))).fv) support_part_0013)
  have support_part_0014 :
    alphaDummy008 ∈ (((synCcompl (Class.cv alphaDummy008))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0014 :
    alphaDummy008 ∈
      (((synCcompl (Class.cv alphaDummy008))).fv ∪
        ((synCcompl (Class.cv alphaDummy009))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy009))).fv) support_part_0014)
  have support_part_0015 : alphaDummy005 ∈ (((Class.cv alphaDummy005)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0015 :
    alphaDummy005 ∈
      (((Class.cv alphaDummy005)).fv ∪ ((Class.cv alphaDummy005)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy005)).fv) support_part_0015)
  have support_part_0016 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0016 :
    alphaDummy008 ∈
      (((Class.cv alphaDummy008)).fv ∪ ((Class.cv alphaDummy008)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy008)).fv) support_part_0016)
  have support_part_0017 :
    alphaDummy006 ∈ (((synCcompl (Class.cv alphaDummy006))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0017 :
    alphaDummy006 ∈
      (((synCcompl (Class.cv alphaDummy005))).fv ∪
        ((synCcompl (Class.cv alphaDummy006))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy005))).fv) support_part_0017)
  have support_part_0018 :
    alphaDummy009 ∈ (((synCcompl (Class.cv alphaDummy009))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0018 :
    alphaDummy009 ∈
      (((synCcompl (Class.cv alphaDummy008))).fv ∪
        ((synCcompl (Class.cv alphaDummy009))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy008))).fv) support_part_0018)
  have support_part_0019 : alphaDummy006 ∈ (((Class.cv alphaDummy006)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0019 :
    alphaDummy006 ∈
      (((Class.cv alphaDummy006)).fv ∪ ((Class.cv alphaDummy006)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy006)).fv) support_part_0019)
  have support_part_0020 : alphaDummy009 ∈ (((Class.cv alphaDummy009)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0020 :
    alphaDummy009 ∈
      (((Class.cv alphaDummy009)).fv ∪ ((Class.cv alphaDummy009)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy009)).fv) support_part_0020)
  have support_part_0021 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0021 :
    alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0021)
  have support_part_0022 :
    alphaDummy030 ∈
      (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0022 :
    alphaDummy030 ∈
      (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv ∪
        ((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv)
        support_part_0022)
  have support_part_0023 : alphaDummy030 ∈ (((Class.cv alphaDummy030)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0023 :
    alphaDummy030 ∈
      (((Class.cv alphaDummy030)).fv ∪ ((Class.cv alphaDummy031)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy031)).fv) support_part_0023)
  have support_part_0024 :
    alphaDummy031 ∈
      (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0024 :
    alphaDummy031 ∈
      (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv ∪
        ((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy030) (Class.cv alphaDummy031))).fv)
        support_part_0024)
  have support_part_0025 : alphaDummy031 ∈ (((Class.cv alphaDummy031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0025 :
    alphaDummy031 ∈
      (((Class.cv alphaDummy030)).fv ∪ ((Class.cv alphaDummy031)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy030)).fv) support_part_0025)
  have support_part_0026 :
    alphaDummy030 ∈ (((synCcompl (Class.cv alphaDummy030))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0026 :
    alphaDummy030 ∈
      (((synCcompl (Class.cv alphaDummy030))).fv ∪
        ((synCcompl (Class.cv alphaDummy031))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy031))).fv) support_part_0026)
  have support_part_0027 : alphaDummy030 ∈ (((Class.cv alphaDummy030)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 :
    alphaDummy030 ∈
      (((Class.cv alphaDummy030)).fv ∪ ((Class.cv alphaDummy030)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy030)).fv) support_part_0027)
  have support_part_0028 :
    alphaDummy031 ∈ (((synCcompl (Class.cv alphaDummy031))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0028 :
    alphaDummy031 ∈
      (((synCcompl (Class.cv alphaDummy030))).fv ∪
        ((synCcompl (Class.cv alphaDummy031))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy030))).fv) support_part_0028)
  have support_part_0029 : alphaDummy031 ∈ (((Class.cv alphaDummy031)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0029 :
    alphaDummy031 ∈
      (((Class.cv alphaDummy031)).fv ∪ ((Class.cv alphaDummy031)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy031)).fv) support_part_0029)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy006, alphaDummy009), (alphaDummy005, alphaDummy008),
        (alphaDummy004, alphaDummy007), (alphaDummy002, alphaDummy003),
        (alphaDummy000, x), (alphaDummy001, y)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy005) (Class.cv alphaDummy006))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy004)
            (synCun (Class.cv alphaDummy005) (Class.cv alphaDummy006)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy008) (Class.cv alphaDummy009))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy007)
            (synCun (Class.cv alphaDummy008) (Class.cv alphaDummy009))))) :=
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
                                  (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv)
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
              (freshVar_injective (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv) (by decide))
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
                                    (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy000)).fv ∪ ((synC1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv x)).fv ∪ ((synC1c)).fv)
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
  have splitAlpha0001 :
    TAlphaWff
      [(alphaDummy031, alphaDummy031), (alphaDummy030, alphaDummy030),
        (alphaDummy029, alphaDummy029), (alphaDummy011, alphaDummy011),
        (alphaDummy010, alphaDummy010), (alphaDummy027, alphaDummy027),
        (alphaDummy026, alphaDummy026), (alphaDummy002, alphaDummy003),
        (alphaDummy000, x), (alphaDummy001, y)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy030) (Class.cv alphaDummy031))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy029)
            (synCun (Class.cv alphaDummy030) (Class.cv alphaDummy031)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy030) (Class.cv alphaDummy031))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy029)
            (synCun (Class.cv alphaDummy030) (Class.cv alphaDummy031))))) :=
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
                                  (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
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
              (freshVar_injective (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
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
                                    (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0027 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0026 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy011)).fv ∪ ((synC1c)).fv)
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
  have splitAlpha0002 :
    TAlphaWff
      [(alphaDummy002, alphaDummy003), (alphaDummy000, x), (alphaDummy001, y)]
      (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
      (Wff.classMem (Class.cv x) (synCnnc)) :=
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
                                  (TAlphaWff.neg splitAlpha0001)))))) (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy010
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy010))
                        (synWral alphaDummy011 (Class.cv alphaDummy010)
                          (Wff.classMem (synCplc (Class.cv alphaDummy011) (synC1c))
                            (Class.cv alphaDummy010)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab alphaDummy010
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy010))
                        (synWral alphaDummy011 (Class.cv alphaDummy010)
                          (Wff.classMem (synCplc (Class.cv alphaDummy011) (synC1c))
                            (Class.cv alphaDummy010)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    ((rcases h with ⟨rfl, rfl⟩));
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
                                  (TAlphaWff.neg splitAlpha0000))))))) splitAlpha0002))
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg splitAlpha0002))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
