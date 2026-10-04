/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001031Sfin. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_sfin`. -/
@[expose]
noncomputable def nominalDfSfin (M : Class) (N : Class) (a : Var) (dv_M_a : a ∉ M.fv)
    (dv_N_a : a ∉ N.fv) :
    Nominal.NPrf
      (synWb (synWsfin M N) (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (synWex a (synWa (.classMem (synCpw1 (.cv a)) M)
              (.classMem (synCpw (.cv a)) N))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((M).fv ∪ (N).fv) 0)
  let alphaDummy001 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy002 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab alphaDummy001
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy001))
            (synWral alphaDummy002 (Class.cv alphaDummy001)
              (Wff.classMem (synCplc (Class.cv alphaDummy002) (synC1c))
                (Class.cv alphaDummy001)))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab alphaDummy001
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy001))
            (synWral alphaDummy002 (Class.cv alphaDummy001)
              (Wff.classMem (synCplc (Class.cv alphaDummy002) (synC1c))
                (Class.cv alphaDummy001)))))).fv) 1)
  let alphaDummy005 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy007 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy008 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy009 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy011 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy012 : Var := (freshVar (((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv ∪
        ((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv) 0)
  let alphaDummy014 : Var :=
    (freshVar (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy011)).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy010))).fv ∪
        ((synCcompl (Class.cv alphaDummy011))).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy010)).fv) 0)
  let alphaDummy017 : Var :=
    (freshVar (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy011)).fv) 0)
  let alphaDummy018 : Var :=
    (freshVar (((synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCnin (synCpw (Class.cv a)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv a)) (synC1c))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((synCpw (Class.cv alphaDummy000))).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy021 : Var := (freshVar (((synCpw (Class.cv a))).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy022 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy023 : Var := (freshVar (((Class.cv a)).fv) 0)
  let alphaDummy024 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv) 0)
  let alphaDummy025 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv ∪
        ((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv) 0)
  let alphaDummy026 : Var :=
    (freshVar (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy027 : Var :=
    (freshVar (((Class.cv alphaDummy023)).fv ∪ ((Class.cv a)).fv) 0)
  have fresh_029 : alphaDummy000 ∉ ((M).fv ∪ (N).fv) := by
    exact freshVar_not_mem ((M).fv ∪ (N).fv) 0
  have support_part_0000 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0000)
  have support_part_0001 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    exact support_part_0001
  have support_part_0002 :
    alphaDummy010 ∈
      (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0002 :
    alphaDummy010 ∈
      (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv ∪
        ((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv)
        support_part_0002)
  have support_part_0003 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 :
    alphaDummy010 ∈
      (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy011)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy011)).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy011 ∈
      (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alphaDummy011 ∈
      (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv ∪
        ((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy010) (Class.cv alphaDummy011))).fv)
        support_part_0004)
  have support_part_0005 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alphaDummy011 ∈
      (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy011)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy010)).fv) support_part_0005)
  have support_part_0006 :
    alphaDummy010 ∈ (((synCcompl (Class.cv alphaDummy010))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0006 :
    alphaDummy010 ∈
      (((synCcompl (Class.cv alphaDummy010))).fv ∪
        ((synCcompl (Class.cv alphaDummy011))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy011))).fv) support_part_0006)
  have support_part_0007 : alphaDummy010 ∈ (((Class.cv alphaDummy010)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alphaDummy010 ∈
      (((Class.cv alphaDummy010)).fv ∪ ((Class.cv alphaDummy010)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy010)).fv) support_part_0007)
  have support_part_0008 :
    alphaDummy011 ∈ (((synCcompl (Class.cv alphaDummy011))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alphaDummy011 ∈
      (((synCcompl (Class.cv alphaDummy010))).fv ∪
        ((synCcompl (Class.cv alphaDummy011))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy010))).fv) support_part_0008)
  have support_part_0009 : alphaDummy011 ∈ (((Class.cv alphaDummy011)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alphaDummy011 ∈
      (((Class.cv alphaDummy011)).fv ∪ ((Class.cv alphaDummy011)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy011)).fv) support_part_0009)
  have support_part_0010 :
    alphaDummy022 ∈
      (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0010 :
    alphaDummy022 ∈
      (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv)
        support_part_0010)
  have support_part_0011 :
    alphaDummy023 ∈ (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0011 :
    alphaDummy023 ∈
      (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv ∪
        ((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv)
        support_part_0011)
  have support_part_0012 : alphaDummy022 ∈ (((Class.cv alphaDummy022)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0012 :
    alphaDummy022 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy000)).fv) support_part_0012)
  have support_part_0013 : alphaDummy023 ∈ (((Class.cv alphaDummy023)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0013 :
    alphaDummy023 ∈ (((Class.cv alphaDummy023)).fv ∪ ((Class.cv a)).fv) := by
    exact (Finset.mem_union_left (((Class.cv a)).fv) support_part_0013)
  have support_part_0014 :
    alphaDummy000 ∈ (((synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c,
      fv_syn_cnin, fv_syn_cpw, eq_self, true_or]
  have support_mem_0014 :
    alphaDummy000 ∈
      (((synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))).fv)
        support_part_0014)
  have support_part_0015 : a ∈ (((synCnin (synCpw (Class.cv a)) (synC1c))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_c1c,
      fv_syn_cnin, fv_syn_cpw, eq_self, true_or]
  have support_mem_0015 :
    a ∈
      (((synCnin (synCpw (Class.cv a)) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv a)) (synC1c))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (synCpw (Class.cv a)) (synC1c))).fv)
        support_part_0015)
  have support_part_0016 :
    alphaDummy000 ∈ (((synCpw (Class.cv alphaDummy000))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]
  have support_mem_0016 :
    alphaDummy000 ∈ (((synCpw (Class.cv alphaDummy000))).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0016)
  have support_part_0017 : a ∈ (((synCpw (Class.cv a))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_cpw, eq_self]
  have support_mem_0017 : a ∈ (((synCpw (Class.cv a))).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0017)
  have support_part_0018 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0018 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    exact support_part_0018
  have support_part_0019 : a ∈ (((Class.cv a)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0019 : a ∈ (((Class.cv a)).fv) := by exact support_part_0019
  have support_part_0020 :
    alphaDummy000 ∈
      (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0020 :
    alphaDummy000 ∈
      (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv ∪
        ((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy022) (Class.cv alphaDummy000))).fv)
        support_part_0020)
  have support_part_0021 :
    a ∈ (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0021 :
    a ∈
      (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv ∪
        ((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (Class.cv alphaDummy023) (Class.cv a))).fv)
        support_part_0021)
  have support_part_0022 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0022 :
    alphaDummy000 ∈
      (((Class.cv alphaDummy022)).fv ∪ ((Class.cv alphaDummy000)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy022)).fv) support_part_0022)
  have support_part_0023 : a ∈ (((Class.cv a)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0023 : a ∈ (((Class.cv alphaDummy023)).fv ∪ ((Class.cv a)).fv) := by
    exact (Finset.mem_union_right (((Class.cv alphaDummy023)).fv) support_part_0023)
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy011, alphaDummy011), (alphaDummy010, alphaDummy010),
        (alphaDummy009, alphaDummy009), (alphaDummy002, alphaDummy002),
        (alphaDummy001, alphaDummy001), (alphaDummy004, alphaDummy004),
        (alphaDummy003, alphaDummy003)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy010) (Class.cv alphaDummy011))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy009)
            (synCun (Class.cv alphaDummy010) (Class.cv alphaDummy011)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy010) (Class.cv alphaDummy011))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy009)
            (synCun (Class.cv alphaDummy010) (Class.cv alphaDummy011))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
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
              (freshVar_injective (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                  (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy002)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  have splitAlpha0001 :
    TAlphaWff [] (Wff.classMem M (synCnnc)) (Wff.classMem M (synCnnc)) :=
    (TAlphaWff.classMem (TAlphaClass.reflOfFvFresh _ _
        (by intro a b h hne; simp only [List.not_mem_nil] at h)) (TAlphaClass.cab (TAlphaWff.all
          (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
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
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg splitAlpha0000)))))) (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy001
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy001))
                        (synWral alphaDummy002 (Class.cv alphaDummy001)
                          (Wff.classMem (synCplc (Class.cv alphaDummy002) (synC1c))
                            (Class.cv alphaDummy001)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab alphaDummy001
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy001))
                        (synWral alphaDummy002 (Class.cv alphaDummy001)
                          (Wff.classMem (synCplc (Class.cv alphaDummy002) (synC1c))
                            (Class.cv alphaDummy001)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))))))
  have splitAlpha0002 :
    TAlphaWff [] (Wff.classMem N (synCnnc)) (Wff.classMem N (synCnnc)) :=
    (TAlphaWff.classMem (TAlphaClass.reflOfFvFresh _ _
        (by intro a b h hne; simp only [List.not_mem_nil] at h)) (TAlphaClass.cab (TAlphaWff.all
          (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.cab (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cab
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
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                      (TAlphaVar.here _ _ _))))) (TAlphaWff.ex (TAlphaWff.conj
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                  (TAlphaWff.neg splitAlpha0000)))))) (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy001
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy001))
                        (synWral alphaDummy002 (Class.cv alphaDummy001)
                          (Wff.classMem (synCplc (Class.cv alphaDummy002) (synC1c))
                            (Class.cv alphaDummy001)))))).fv) (by decide)) (freshVar_injective
                  (((Class.cab alphaDummy001
                      (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy001))
                        (synWral alphaDummy002 (Class.cv alphaDummy001)
                          (Wff.classMem (synCplc (Class.cv alphaDummy002) (synC1c))
                            (Class.cv alphaDummy001)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))))))
  have splitAlpha0003 :
    TAlphaWff [(alphaDummy018, alphaDummy019), (alphaDummy000, a)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy018)
          (synCnin (synCpw (Class.cv alphaDummy000)) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy018)
            (synCnin (synCpw (Class.cv alphaDummy000)) (synC1c)))))
      (Wff.imp (Wff.classMem (Class.cv alphaDummy019)
          (synCnin (synCpw (Class.cv a)) (synC1c))) (Wff.neg
          (Wff.classMem (Class.cv alphaDummy019)
            (synCnin (synCpw (Class.cv a)) (synC1c))))) :=
    (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.here _ _ _))))))))))))
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.here _ _ _)))))))))))))))
                    (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (freshVar_injective ((∅ : Finset Var)) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.here _ _ _))))))))))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
            (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.here _ _ _))))))))))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0012 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0013 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                        (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0022 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0023 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0016 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0017 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0014 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0015 0)) (TAlphaVar.here _ _ _)))))))))))))))
                      (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (freshVar_injective ((∅ : Finset Var)) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  change
    Nominal.NPrf
      (Wff.biimp (synWsfin M N)
        (synW3a (Wff.classMem M (synCnnc)) (Wff.classMem N (synCnnc)) (synWex a
            (synWa (Wff.classMem (synCpw1 (Class.cv a)) M)
              (Wff.classMem (synCpw (Class.cv a)) N)))))
  exact
    Nominal.alphaBiimp
      (TAlphaWff.conj (TAlphaWff.conj splitAlpha0001 splitAlpha0002) (TAlphaWff.ex
          (TAlphaWff.conj (TAlphaWff.classMem
              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg splitAlpha0003)))
              (TAlphaClass.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.classEq
                  (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.here _ _ _))))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0010 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0011 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0022 0))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0023 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0020 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0021 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0018 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0019 0)) (TAlphaVar.here _ _ _)))))))))))))
                  (TAlphaClass.cv (TAlphaVar.here _ _ _)))) (TAlphaClass.reflOfFvFresh _ _
                (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
