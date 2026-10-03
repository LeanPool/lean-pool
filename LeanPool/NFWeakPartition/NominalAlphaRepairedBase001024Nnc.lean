/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001024Nnc. -/


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
noncomputable def nominal_df_nnc (y : Var) (b : Var) (dv_b_y : b ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cnnc) (syn_cint (.cab b (syn_wa (.classMem (syn_c0c) (.cv b))
              (syn_wral y (.cv b) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv b))))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alpha_dummy_002 : Var :=
    (freshVar (((Class.cab alpha_dummy_000
          (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
            (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
              (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                (Class.cv alpha_dummy_000)))))).fv) 0)
  let alpha_dummy_003 : Var :=
    (freshVar (((Class.cab alpha_dummy_000
          (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
            (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
              (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                (Class.cv alpha_dummy_000)))))).fv) 1)
  let alpha_dummy_004 : Var :=
    (freshVar (((Class.cab b (syn_wa (Wff.classMem (syn_c0c) (Class.cv b))
            (syn_wral y (Class.cv b)
              (Wff.classMem (syn_cplc (Class.cv y) (syn_c1c)) (Class.cv b)))))).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cab b (syn_wa (Wff.classMem (syn_c0c) (Class.cv b))
            (syn_wral y (Class.cv b)
              (Wff.classMem (syn_cplc (Class.cv y) (syn_c1c)) (Class.cv b)))))).fv) 1)
  let alpha_dummy_006 : Var := (freshVar (((syn_c0)).fv) 0)
  let alpha_dummy_007 : Var :=
    (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪
        ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_009 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_010 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_011 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_012 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_013 : Var := (freshVar (((Class.cv y)).fv ∪ ((syn_c1c)).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((Class.cv y)).fv ∪ ((syn_c1c)).fv) 1)
  let alpha_dummy_015 : Var := (freshVar (((Class.cv y)).fv ∪ ((syn_c1c)).fv) 2)
  let alpha_dummy_016 : Var := (freshVar (((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_017 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv) 0)
  let alpha_dummy_018 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv) 0)
  let alpha_dummy_019 : Var :=
    (freshVar (((Class.cv alpha_dummy_011)).fv ∪ ((Class.cv alpha_dummy_012)).fv) 0)
  let alpha_dummy_020 : Var :=
    (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_015)).fv) 0)
  let alpha_dummy_021 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_011))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_012))).fv) 0)
  let alpha_dummy_022 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_014))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_015))).fv) 0)
  let alpha_dummy_023 : Var :=
    (freshVar (((Class.cv alpha_dummy_011)).fv ∪ ((Class.cv alpha_dummy_011)).fv) 0)
  let alpha_dummy_024 : Var :=
    (freshVar (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_014)).fv) 0)
  let alpha_dummy_025 : Var :=
    (freshVar (((Class.cv alpha_dummy_012)).fv ∪ ((Class.cv alpha_dummy_012)).fv) 0)
  let alpha_dummy_026 : Var :=
    (freshVar (((Class.cv alpha_dummy_015)).fv ∪ ((Class.cv alpha_dummy_015)).fv) 0)
  have support_part_0000 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0000)
  have support_part_0001 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : y ∈ (((Class.cv y)).fv ∪ ((syn_c1c)).fv) := by
    exact (Finset.mem_union_left (((syn_c1c)).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    exact support_part_0002
  have support_part_0003 :
    alpha_dummy_011 ∈
      (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0003 :
    alpha_dummy_011 ∈
      (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv)
        support_part_0003)
  have support_part_0004 :
    alpha_dummy_014 ∈
      (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0004 :
    alpha_dummy_014 ∈
      (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv)
        support_part_0004)
  have support_part_0005 : alpha_dummy_011 ∈ (((Class.cv alpha_dummy_011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alpha_dummy_011 ∈
      (((Class.cv alpha_dummy_011)).fv ∪ ((Class.cv alpha_dummy_012)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_012)).fv) support_part_0005)
  have support_part_0006 : alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 :
    alpha_dummy_014 ∈
      (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_015)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_015)).fv) support_part_0006)
  have support_part_0007 :
    alpha_dummy_012 ∈
      (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0007 :
    alpha_dummy_012 ∈
      (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))).fv)
        support_part_0007)
  have support_part_0008 :
    alpha_dummy_015 ∈
      (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0008 :
    alpha_dummy_015 ∈
      (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))).fv)
        support_part_0008)
  have support_part_0009 : alpha_dummy_012 ∈ (((Class.cv alpha_dummy_012)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alpha_dummy_012 ∈
      (((Class.cv alpha_dummy_011)).fv ∪ ((Class.cv alpha_dummy_012)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_011)).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_015 ∈ (((Class.cv alpha_dummy_015)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 :
    alpha_dummy_015 ∈
      (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_015)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_014)).fv) support_part_0010)
  have support_part_0011 :
    alpha_dummy_011 ∈ (((syn_ccompl (Class.cv alpha_dummy_011))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0011 :
    alpha_dummy_011 ∈
      (((syn_ccompl (Class.cv alpha_dummy_011))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_012))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_012))).fv) support_part_0011)
  have support_part_0012 :
    alpha_dummy_014 ∈ (((syn_ccompl (Class.cv alpha_dummy_014))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0012 :
    alpha_dummy_014 ∈
      (((syn_ccompl (Class.cv alpha_dummy_014))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_015))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_015))).fv) support_part_0012)
  have support_part_0013 : alpha_dummy_011 ∈ (((Class.cv alpha_dummy_011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0013 :
    alpha_dummy_011 ∈
      (((Class.cv alpha_dummy_011)).fv ∪ ((Class.cv alpha_dummy_011)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_011)).fv) support_part_0013)
  have support_part_0014 : alpha_dummy_014 ∈ (((Class.cv alpha_dummy_014)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alpha_dummy_014 ∈
      (((Class.cv alpha_dummy_014)).fv ∪ ((Class.cv alpha_dummy_014)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_014)).fv) support_part_0014)
  have support_part_0015 :
    alpha_dummy_012 ∈ (((syn_ccompl (Class.cv alpha_dummy_012))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0015 :
    alpha_dummy_012 ∈
      (((syn_ccompl (Class.cv alpha_dummy_011))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_012))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_011))).fv) support_part_0015)
  have support_part_0016 :
    alpha_dummy_015 ∈ (((syn_ccompl (Class.cv alpha_dummy_015))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0016 :
    alpha_dummy_015 ∈
      (((syn_ccompl (Class.cv alpha_dummy_014))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_015))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_014))).fv) support_part_0016)
  have support_part_0017 : alpha_dummy_012 ∈ (((Class.cv alpha_dummy_012)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0017 :
    alpha_dummy_012 ∈
      (((Class.cv alpha_dummy_012)).fv ∪ ((Class.cv alpha_dummy_012)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_012)).fv) support_part_0017)
  have support_part_0018 : alpha_dummy_015 ∈ (((Class.cv alpha_dummy_015)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0018 :
    alpha_dummy_015 ∈
      (((Class.cv alpha_dummy_015)).fv ∪ ((Class.cv alpha_dummy_015)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_015)).fv) support_part_0018)
  have split_alpha_0000 :
    TAlphaWff
      [(alpha_dummy_012, alpha_dummy_015), (alpha_dummy_011, alpha_dummy_014),
        (alpha_dummy_010, alpha_dummy_013), (alpha_dummy_001, y), (alpha_dummy_000, b),
        (alpha_dummy_003, alpha_dummy_005), (alpha_dummy_002, alpha_dummy_004)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_010)
            (syn_cun (Class.cv alpha_dummy_011) (Class.cv alpha_dummy_012)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_013)
            (syn_cun (Class.cv alpha_dummy_014) (Class.cv alpha_dummy_015))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv y)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv y)).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
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
              (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv y)).fv ∪ ((syn_c1c)).fv) (by decide))
              (TAlphaVar.there
                (freshVar_injective (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv y)).fv ∪ ((syn_c1c)).fv) (by decide))
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv y)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alpha_dummy_001)).fv ∪ ((syn_c1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv y)).fv ∪ ((syn_c1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0017 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0018 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0016 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  exact
    Nominal.alphaClassEq
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
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_y
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.classMem (TAlphaClass.cab
                          (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                      (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg split_alpha_0000)))))) (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_y
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alpha_dummy_000
                      (syn_wa (Wff.classMem (syn_c0c) (Class.cv alpha_dummy_000))
                        (syn_wral alpha_dummy_001 (Class.cv alpha_dummy_000)
                          (Wff.classMem (syn_cplc (Class.cv alpha_dummy_001) (syn_c1c))
                            (Class.cv alpha_dummy_000)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab b (syn_wa (Wff.classMem (syn_c0c) (Class.cv b))
                        (syn_wral y (Class.cv b) (Wff.classMem (syn_cplc (Class.cv y) (syn_c1c))
                            (Class.cv b)))))).fv) (by decide)) (TAlphaVar.here _ _ _))
              (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
