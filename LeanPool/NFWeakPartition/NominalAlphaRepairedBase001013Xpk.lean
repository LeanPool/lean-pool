/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001013Xpk. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_xpk`. -/
@[expose]
noncomputable def nominalDfXpk (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCxpk A B) (.cab x (synWex y (synWex z
              (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
                (synWa (.classMem (.cv y) A) (.classMem (.cv z) B))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alphaDummy002 : Var := (freshVar ((A).fv ∪ (B).fv) 2)
  let alphaDummy003 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv ∪ ((synCcompl
            (synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((synCcompl (synCsn (synCsn (Class.cv y))))).fv ∪
        ((synCcompl (synCsn (synCpr (Class.cv y) (Class.cv z))))).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy001)))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) 0)
  let alphaDummy007 : Var := (freshVar (((synCsn (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy008 : Var := (freshVar (((synCsn (Class.cv y))).fv) 0)
  let alphaDummy009 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy010 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv ∪
        ((synCsn (synCpr (Class.cv y) (Class.cv z)))).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy014 : Var := (freshVar (((synCpr (Class.cv y) (Class.cv z))).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((synCcompl (synCsn (Class.cv y)))).fv ∪
        ((synCcompl (synCsn (Class.cv z)))).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy001))).fv ∪
        ((synCsn (Class.cv alphaDummy001))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCsn (Class.cv alphaDummy002))).fv ∪
        ((synCsn (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) 0)
  let alphaDummy021 : Var := (freshVar (((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy022 : Var := (freshVar (((Class.cv z)).fv) 0)
  have fresh_020 : alphaDummy000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_021 : alphaDummy001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have fresh_022 : alphaDummy002 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 2
  have support_part_0000 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv)
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
    alphaDummy001 ∈ (((synCsn (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alphaDummy001 ∈
      (((synCsn (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCsn (synCsn (Class.cv alphaDummy001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv alphaDummy001)))).fv)
        support_part_0002)
  have support_part_0003 : y ∈ (((synCsn (synCsn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    y ∈ (((synCsn (synCsn (Class.cv y)))).fv ∪ ((synCsn (synCsn (Class.cv y)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (synCsn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) :=
    by exact support_part_0004
  have support_part_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : y ∈ (((synCsn (Class.cv y))).fv) := by exact support_part_0005
  have support_part_0006 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by exact support_part_0007
  have support_part_0008 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alphaDummy001 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv)
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
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy001 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by exact support_part_0010
  have support_part_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : y ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alphaDummy001 ∈ (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alphaDummy001 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv)
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
    alphaDummy001 ∈ (((synCsn (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alphaDummy001 ∈
      (((synCsn (Class.cv alphaDummy001))).fv ∪ ((synCsn (Class.cv alphaDummy001))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy001))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((synCsn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    y ∈ (((synCsn (Class.cv y))).fv ∪ ((synCsn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy002 ∈
      (((synCcompl (synCsn
            (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv ∪ ((synCcompl (synCsn
              (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (synCsn (Class.cv alphaDummy001))))).fv)
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
    alphaDummy002 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alphaDummy002 ∈
      (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv ∪
        ((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCsn (synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002)))).fv)
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
    alphaDummy002 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy002 ∈
      (((synCpr (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by exact support_part_0020
  have support_part_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : z ∈ (((synCpr (Class.cv y) (Class.cv z))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alphaDummy002 ∈ (((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alphaDummy002 ∈
      (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv ∪
        ((synCcompl (synCsn (Class.cv alphaDummy002)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (synCsn (Class.cv alphaDummy001)))).fv)
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
    alphaDummy002 ∈ (((synCsn (Class.cv alphaDummy002))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alphaDummy002 ∈
      (((synCsn (Class.cv alphaDummy002))).fv ∪ ((synCsn (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCsn (Class.cv alphaDummy002))).fv) support_part_0024)
  have support_part_0025 : z ∈ (((synCsn (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    z ∈ (((synCsn (Class.cv z))).fv ∪ ((synCsn (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((synCsn (Class.cv z))).fv) support_part_0025)
  have support_part_0026 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    exact support_part_0026
  have support_part_0027 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : z ∈ (((Class.cv z)).fv) := by exact support_part_0027
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy015, alphaDummy016), (alphaDummy013, alphaDummy014),
        (alphaDummy011, alphaDummy012), (alphaDummy003, alphaDummy004),
        (alphaDummy002, z), (alphaDummy001, y), (alphaDummy000, x)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy015)
          (synCcompl (synCsn (Class.cv alphaDummy001)))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy015)
            (synCcompl (synCsn (Class.cv alphaDummy002))))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy016) (synCcompl (synCsn (Class.cv y))))
        (Wff.neg (Wff.classMem (Class.cv alphaDummy016)
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
                                    (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
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
                                    (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
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
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq
                (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_z
                    (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
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
        (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z
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
        (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z
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
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                      dv_y_z (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfFvFresh _ _ (by
                      intro a b h hne;
                      simp only [List.mem_cons, List.not_mem_nil, or_false,
                        Prod.mk.injEq] at h;
                      repeat'
                        (first
                          | (rcases h with ⟨rfl, rfl⟩));
                        all_goals aesop)))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfFvFresh _ _ (by
                      intro a b h hne;
                      simp only [List.mem_cons, List.not_mem_nil, or_false,
                        Prod.mk.injEq] at h;
                      repeat'
                        (first
                          | (rcases h with ⟨rfl, rfl⟩));
                        all_goals aesop))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
