/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001017Imak. -/


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
noncomputable def nominal_df_imak (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cimak A B)
        (.cab x (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alpha_dummy_002 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl
            (syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))))).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv x))))).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((syn_csn (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_007 : Var := (freshVar (((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((Class.cv y)).fv) 0)
  let alpha_dummy_010 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv) 0)
  let alpha_dummy_011 : Var :=
    (freshVar (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv) 0)
  let alpha_dummy_012 : Var :=
    (freshVar (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_013 : Var := (freshVar (((syn_cpr (Class.cv y) (Class.cv x))).fv) 0)
  let alpha_dummy_014 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv) 0)
  let alpha_dummy_015 : Var :=
    (freshVar (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv x)))).fv) 0)
  let alpha_dummy_016 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_001))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_001))).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) 0)
  let alpha_dummy_018 : Var :=
    (freshVar (((syn_csn (Class.cv alpha_dummy_000))).fv ∪
        ((syn_csn (Class.cv alpha_dummy_000))).fv) 0)
  let alpha_dummy_019 : Var :=
    (freshVar (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) 0)
  let alpha_dummy_020 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv) 0)
  let alpha_dummy_021 : Var := (freshVar (((Class.cv x)).fv) 0)
  have fresh_020 : alpha_dummy_000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_021 : alpha_dummy_001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have support_part_0000 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv) :=
    by simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0000 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))))).fv)
        support_part_0000)
  have support_part_0001 : y ∈ (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0001 :
    y ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv x))))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv x))))).fv)
        support_part_0001)
  have support_part_0002 :
    alpha_dummy_001 ∈ (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0002 :
    alpha_dummy_001 ∈
      (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv alpha_dummy_001)))).fv)
        support_part_0002)
  have support_part_0003 : y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0003 :
    y ∈ (((syn_csn (syn_csn (Class.cv y)))).fv ∪ ((syn_csn (syn_csn (Class.cv y)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_csn (Class.cv y)))).fv) support_part_0003)
  have support_part_0004 :
    alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0004 : alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) :=
    by exact support_part_0004
  have support_part_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0005 : y ∈ (((syn_csn (Class.cv y))).fv) := by exact support_part_0005
  have support_part_0006 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0006
  have support_part_0007 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : y ∈ (((Class.cv y)).fv) := by exact support_part_0007
  have support_part_0008 :
    alpha_dummy_001 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0008 :
    alpha_dummy_001 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv)
        support_part_0008)
  have support_part_0009 : y ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, true_or]
  have support_mem_0009 :
    y ∈
      (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv)
        support_part_0009)
  have support_part_0010 :
    alpha_dummy_001 ∈
      (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0010 :
    alpha_dummy_001 ∈
      (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))).fv) :=
    by exact support_part_0010
  have support_part_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv x))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      true_or]
  have support_mem_0011 : y ∈ (((syn_cpr (Class.cv y) (Class.cv x))).fv) := by
    exact support_part_0011
  have support_part_0012 :
    alpha_dummy_001 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0012 :
    alpha_dummy_001 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv)
        support_part_0012)
  have support_part_0013 : y ∈ (((syn_ccompl (syn_csn (Class.cv y)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0013 :
    y ∈
      (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv x)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (syn_csn (Class.cv x)))).fv) support_part_0013)
  have support_part_0014 :
    alpha_dummy_001 ∈ (((syn_csn (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0014 :
    alpha_dummy_001 ∈
      (((syn_csn (Class.cv alpha_dummy_001))).fv ∪ ((syn_csn (Class.cv alpha_dummy_001))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_001))).fv) support_part_0014)
  have support_part_0015 : y ∈ (((syn_csn (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0015 :
    y ∈ (((syn_csn (Class.cv y))).fv ∪ ((syn_csn (Class.cv y))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv y))).fv) support_part_0015)
  have support_part_0016 :
    alpha_dummy_000 ∈
      (((syn_ccompl (syn_csn
            (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0016 :
    alpha_dummy_000 ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv ∪ ((syn_ccompl (syn_csn
              (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv alpha_dummy_001))))).fv)
        support_part_0016)
  have support_part_0017 :
    x ∈ (((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv x))))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_ccompl,
      fv_syn_cpr, fv_syn_csn, eq_self, or_true]
  have support_mem_0017 :
    x ∈
      (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_cpr (Class.cv y) (Class.cv x))))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (syn_csn (Class.cv y))))).fv)
        support_part_0017)
  have support_part_0018 :
    alpha_dummy_000 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0018 :
    alpha_dummy_000 ∈
      (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_csn (syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000)))).fv)
        support_part_0018)
  have support_part_0019 : x ∈ (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr,
      fv_syn_csn, eq_self, or_true]
  have support_mem_0019 :
    x ∈
      (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv ∪
        ((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (syn_cpr (Class.cv y) (Class.cv x)))).fv)
        support_part_0019)
  have support_part_0020 :
    alpha_dummy_000 ∈
      (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0020 :
    alpha_dummy_000 ∈
      (((syn_cpr (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_000))).fv) :=
    by exact support_part_0020
  have support_part_0021 : x ∈ (((syn_cpr (Class.cv y) (Class.cv x))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cpr, eq_self,
      or_true]
  have support_mem_0021 : x ∈ (((syn_cpr (Class.cv y) (Class.cv x))).fv) := by
    exact support_part_0021
  have support_part_0022 :
    alpha_dummy_000 ∈ (((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0022 :
    alpha_dummy_000 ∈
      (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv ∪
        ((syn_ccompl (syn_csn (Class.cv alpha_dummy_000)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))).fv)
        support_part_0022)
  have support_part_0023 : x ∈ (((syn_ccompl (syn_csn (Class.cv x)))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, fv_syn_csn, eq_self]
  have support_mem_0023 :
    x ∈
      (((syn_ccompl (syn_csn (Class.cv y)))).fv ∪ ((syn_ccompl (syn_csn (Class.cv x)))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (syn_csn (Class.cv y)))).fv) support_part_0023)
  have support_part_0024 :
    alpha_dummy_000 ∈ (((syn_csn (Class.cv alpha_dummy_000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0024 :
    alpha_dummy_000 ∈
      (((syn_csn (Class.cv alpha_dummy_000))).fv ∪ ((syn_csn (Class.cv alpha_dummy_000))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_csn (Class.cv alpha_dummy_000))).fv) support_part_0024)
  have support_part_0025 : x ∈ (((syn_csn (Class.cv x))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_csn, eq_self]
  have support_mem_0025 :
    x ∈ (((syn_csn (Class.cv x))).fv ∪ ((syn_csn (Class.cv x))).fv) := by
    exact (Finset.mem_union_left (((syn_csn (Class.cv x))).fv) support_part_0025)
  have support_part_0026 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0026 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    exact support_part_0026
  have support_part_0027 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0027 : x ∈ (((Class.cv x)).fv) := by exact support_part_0027
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_014, alpha_dummy_015), (alpha_dummy_012, alpha_dummy_013),
        (alpha_dummy_010, alpha_dummy_011), (alpha_dummy_002, alpha_dummy_003),
        (alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_014)
          (syn_ccompl (syn_csn (Class.cv alpha_dummy_001)))) (Wff.neg
          (Wff.classMem (Class.cv alpha_dummy_014)
            (syn_ccompl (syn_csn (Class.cv alpha_dummy_000))))))
      (Wff.imp (Wff.classMem (Class.cv alpha_dummy_015) (syn_ccompl (syn_csn (Class.cv y))))
        (Wff.neg (Wff.classMem (Class.cv alpha_dummy_015)
            (syn_ccompl (syn_csn (Class.cv x)))))) :=
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
                                  (TAlphaVar.here _ _ _)))))))))))
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
                                  (TAlphaVar.here _ _ _))))))))))))))) (TAlphaWff.neg
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
                                    (TAlphaVar.there
                                      (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                      dv_x_y (TAlphaVar.here _ _ _))))))))))))
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
                                    (TAlphaVar.there
                                      (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                      dv_x_y (TAlphaVar.here _ _ _))))))))))))))))))
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
                    all_goals aesop))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab
                                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.cab (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0006 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0004 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0002 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))))))))
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
                                  (TAlphaClass.cab (TAlphaWff.neg
                                      (TAlphaWff.neg split_alpha_0000)))))))))))))
              (TAlphaClass.refl_of_fv_fresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
