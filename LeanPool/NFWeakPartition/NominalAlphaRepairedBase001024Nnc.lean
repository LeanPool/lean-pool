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

/-- Checked nominal proof certificate identified upstream as `nominal_df_nnc`. -/
@[expose]
noncomputable def nominalDfNnc (y : Var) (b : Var) (dv_b_y : b ≠ y) :
    Nominal.NPrf
      (.classEq (synCnnc) (synCint (.cab b (synWa (.classMem (synC0c) (.cv b))
              (synWral y (.cv b) (.classMem (synCplc (.cv y) (synC1c)) (.cv b))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy001 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy002 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
            (synWral alphaDummy001 (Class.cv alphaDummy000)
              (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                (Class.cv alphaDummy000)))))).fv) 1)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab b (synWa (Wff.classMem (synC0c) (Class.cv b))
            (synWral y (Class.cv b)
              (Wff.classMem (synCplc (Class.cv y) (synC1c)) (Class.cv b)))))).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cab b (synWa (Wff.classMem (synC0c) (Class.cv b))
            (synWral y (Class.cv b)
              (Wff.classMem (synCplc (Class.cv y) (synC1c)) (Class.cv b)))))).fv) 1)
  let alphaDummy006 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy008 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy009 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy012 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy013 : Var := (freshVar (((Class.cv y)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy014 : Var := (freshVar (((Class.cv y)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy015 : Var := (freshVar (((Class.cv y)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy016 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv ∪
        ((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv ∪
        ((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy012)).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy015)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy011))).fv ∪
        ((synCcompl (Class.cv alphaDummy012))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy014))).fv ∪
        ((synCcompl (Class.cv alphaDummy015))).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy011)).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy014)).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy012)).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy015)).fv) 0)
  have support_part_0000 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0000)
  have support_part_0001 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : y ∈ (((Class.cv y)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0001)
  have support_part_0002 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0002
  have support_part_0003 :
    alphaDummy011 ∈
      (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0003 :
    alphaDummy011 ∈
      (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv ∪
        ((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv)
        support_part_0003)
  have support_part_0004 :
    alphaDummy014 ∈
      (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0004 :
    alphaDummy014 ∈
      (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv ∪
        ((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv)
        support_part_0004)
  have support_part_0005 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alphaDummy011 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy012)).fv) support_part_0005)
  have support_part_0006 : alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 :
    alphaDummy014 ∈
      (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy015)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy015)).fv) support_part_0006)
  have support_part_0007 :
    alphaDummy012 ∈
      (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0007 :
    alphaDummy012 ∈
      (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv ∪
        ((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy011) (Class.cv alphaDummy012))).fv)
        support_part_0007)
  have support_part_0008 :
    alphaDummy015 ∈
      (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0008 :
    alphaDummy015 ∈
      (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv ∪
        ((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy014) (Class.cv alphaDummy015))).fv)
        support_part_0008)
  have support_part_0009 : alphaDummy012 ∈ (((Class.cv alphaDummy012)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alphaDummy012 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy011)).fv) support_part_0009)
  have support_part_0010 : alphaDummy015 ∈ (((Class.cv alphaDummy015)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 :
    alphaDummy015 ∈
      (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy015)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy014)).fv) support_part_0010)
  have support_part_0011 :
    alphaDummy011 ∈ (((synCcompl (Class.cv alphaDummy011))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0011 :
    alphaDummy011 ∈
      (((synCcompl (Class.cv alphaDummy011))).fv ∪
        ((synCcompl (Class.cv alphaDummy012))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy012))).fv) support_part_0011)
  have support_part_0012 :
    alphaDummy014 ∈ (((synCcompl (Class.cv alphaDummy014))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0012 :
    alphaDummy014 ∈
      (((synCcompl (Class.cv alphaDummy014))).fv ∪
        ((synCcompl (Class.cv alphaDummy015))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy015))).fv) support_part_0012)
  have support_part_0013 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0013 :
    alphaDummy011 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy011)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy011)).fv) support_part_0013)
  have support_part_0014 : alphaDummy014 ∈ (((Class.cv alphaDummy014)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alphaDummy014 ∈
      (((Class.cv alphaDummy014)).fv ∪ ((Class.cv alphaDummy014)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy014)).fv) support_part_0014)
  have support_part_0015 :
    alphaDummy012 ∈ (((synCcompl (Class.cv alphaDummy012))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0015 :
    alphaDummy012 ∈
      (((synCcompl (Class.cv alphaDummy011))).fv ∪
        ((synCcompl (Class.cv alphaDummy012))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy011))).fv) support_part_0015)
  have support_part_0016 :
    alphaDummy015 ∈ (((synCcompl (Class.cv alphaDummy015))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0016 :
    alphaDummy015 ∈
      (((synCcompl (Class.cv alphaDummy014))).fv ∪
        ((synCcompl (Class.cv alphaDummy015))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy014))).fv) support_part_0016)
  have support_part_0017 : alphaDummy012 ∈ (((Class.cv alphaDummy012)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0017 :
    alphaDummy012 ∈
      (((Class.cv alphaDummy012)).fv ∪ ((Class.cv alphaDummy012)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy012)).fv) support_part_0017)
  have support_part_0018 : alphaDummy015 ∈ (((Class.cv alphaDummy015)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0018 :
    alphaDummy015 ∈
      (((Class.cv alphaDummy015)).fv ∪ ((Class.cv alphaDummy015)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy015)).fv) support_part_0018)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy012, alphaDummy015), (alphaDummy011, alphaDummy014),
        (alphaDummy010, alphaDummy013), (alphaDummy001, y), (alphaDummy000, b),
        (alphaDummy003, alphaDummy005), (alphaDummy002, alphaDummy004)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy011) (Class.cv alphaDummy012))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy010)
            (synCun (Class.cv alphaDummy011) (Class.cv alphaDummy012)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy014) (Class.cv alphaDummy015))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy013)
            (synCun (Class.cv alphaDummy014) (Class.cv alphaDummy015))))) :=
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
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv y)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                  (by decide))
                                (freshVar_injective (((Class.cv y)).fv ∪ ((synC1c)).fv)
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
              (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv y)).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv y)).fv ∪ ((synC1c)).fv) (by decide))
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
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv y)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy001)).fv ∪ ((synC1c)).fv)
                                    (by decide))
                                  (freshVar_injective (((Class.cv y)).fv ∪ ((synC1c)).fv)
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
                                  (TAlphaWff.neg splitAlpha0000)))))) (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_b_y
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy000
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy000))
                        (synWral alphaDummy001 (Class.cv alphaDummy000)
                          (Wff.classMem (synCplc (Class.cv alphaDummy001) (synC1c))
                            (Class.cv alphaDummy000)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab b (synWa (Wff.classMem (synC0c) (Class.cv b))
                        (synWral y (Class.cv b) (Wff.classMem (synCplc (Class.cv y) (synC1c))
                            (Class.cv b)))))).fv) (by decide)) (TAlphaVar.here _ _ _))
              (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
