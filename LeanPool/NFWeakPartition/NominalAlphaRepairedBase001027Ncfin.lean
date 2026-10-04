/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001027Ncfin. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_ncfin`. -/
@[expose]
noncomputable def nominalDfNcfin (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.classEq (synCncfin A)
        (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var :=
    (freshVar (({ alphaDummy000 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
            (Wff.classMem A (Class.cv alphaDummy000)))).fv) 0)
  let alphaDummy002 : Var :=
    (freshVar (({ x } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv x) (synCnnc))
            (Wff.classMem A (Class.cv x)))).fv) 0)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab alphaDummy001 (Wff.classEq (Class.cab alphaDummy000
              (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                (Wff.classMem A (Class.cv alphaDummy000))))
            (synCsn (Class.cv alphaDummy001))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab alphaDummy001 (Wff.classEq (Class.cab alphaDummy000
              (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                (Wff.classMem A (Class.cv alphaDummy000))))
            (synCsn (Class.cv alphaDummy001))))).fv) 1)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
              (synWa (Wff.classMem (Class.cv x) (synCnnc)) (Wff.classMem A (Class.cv x))))
            (synCsn (Class.cv alphaDummy002))))).fv) 0)
  let alphaDummy006 : Var :=
    (freshVar (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
              (synWa (Wff.classMem (Class.cv x) (synCnnc)) (Wff.classMem A (Class.cv x))))
            (synCsn (Class.cv alphaDummy002))))).fv) 1)
  let alphaDummy007 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy008 : Var := (freshVar ((∅ : Finset Var)) 1)
  let alphaDummy009 : Var :=
    (freshVar (((Class.cab alphaDummy007
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy007))
            (synWral alphaDummy008 (Class.cv alphaDummy007)
              (Wff.classMem (synCplc (Class.cv alphaDummy008) (synC1c))
                (Class.cv alphaDummy007)))))).fv) 0)
  let alphaDummy010 : Var :=
    (freshVar (((Class.cab alphaDummy007
          (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy007))
            (synWral alphaDummy008 (Class.cv alphaDummy007)
              (Wff.classMem (synCplc (Class.cv alphaDummy008) (synC1c))
                (Class.cv alphaDummy007)))))).fv) 1)
  let alphaDummy011 : Var := (freshVar (((synC0)).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy013 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy014 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) 0)
  let alphaDummy016 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) 1)
  let alphaDummy017 : Var :=
    (freshVar (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) 2)
  let alphaDummy018 : Var := (freshVar (((Class.cv alphaDummy008)).fv) 0)
  let alphaDummy019 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv ∪
        ((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) 0)
  let alphaDummy020 : Var :=
    (freshVar (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy017)).fv) 0)
  let alphaDummy021 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy016))).fv ∪
        ((synCcompl (Class.cv alphaDummy017))).fv) 0)
  let alphaDummy022 : Var :=
    (freshVar (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy016)).fv) 0)
  let alphaDummy023 : Var :=
    (freshVar (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy017)).fv) 0)
  let alphaDummy024 : Var := (freshVar (((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy025 : Var := (freshVar (((Class.cv alphaDummy002)).fv) 0)
  have fresh_000 :
    alphaDummy003 ∉
      (((Class.cab alphaDummy001 (Wff.classEq (Class.cab alphaDummy000
              (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                (Wff.classMem A (Class.cv alphaDummy000))))
            (synCsn (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy001 (Wff.classEq (Class.cab alphaDummy000
                (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                  (Wff.classMem A (Class.cv alphaDummy000))))
              (synCsn (Class.cv alphaDummy001))))).fv)
        0
  have fresh_001 :
    alphaDummy004 ∉
      (((Class.cab alphaDummy001 (Wff.classEq (Class.cab alphaDummy000
              (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                (Wff.classMem A (Class.cv alphaDummy000))))
            (synCsn (Class.cv alphaDummy001))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy001 (Wff.classEq (Class.cab alphaDummy000
                (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                  (Wff.classMem A (Class.cv alphaDummy000))))
              (synCsn (Class.cv alphaDummy001))))).fv)
        1
  have fresh_003 :
    alphaDummy005 ∉
      (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
              (synWa (Wff.classMem (Class.cv x) (synCnnc)) (Wff.classMem A (Class.cv x))))
            (synCsn (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
                (synWa (Wff.classMem (Class.cv x) (synCnnc)) (Wff.classMem A (Class.cv x))))
              (synCsn (Class.cv alphaDummy002))))).fv)
        0
  have fresh_004 :
    alphaDummy006 ∉
      (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
              (synWa (Wff.classMem (Class.cv x) (synCnnc)) (Wff.classMem A (Class.cv x))))
            (synCsn (Class.cv alphaDummy002))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
                (synWa (Wff.classMem (Class.cv x) (synCnnc)) (Wff.classMem A (Class.cv x))))
              (synCsn (Class.cv alphaDummy002))))).fv)
        1
  have fresh_027 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_028 :
    alphaDummy001 ∉
      (({ alphaDummy000 } : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
            (Wff.classMem A (Class.cv alphaDummy000)))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ alphaDummy000 } : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
              (Wff.classMem A (Class.cv alphaDummy000)))).fv)
        0
  have fresh_029 :
    alphaDummy002 ∉
      (({ x } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv x) (synCnnc))
            (Wff.classMem A (Class.cv x)))).fv) :=
    by
    exact
      freshVar_not_mem
        (({ x } : Finset Var) ∪ ((synWa (Wff.classMem (Class.cv x) (synCnnc))
              (Wff.classMem A (Class.cv x)))).fv)
        0
  have support_part_0000 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 :
    alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv) := by
    exact (Finset.mem_union_left (((synC1c)).fv) support_part_0000)
  have support_part_0001 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : alphaDummy008 ∈ (((Class.cv alphaDummy008)).fv) := by
    exact support_part_0001
  have support_part_0002 :
    alphaDummy016 ∈
      (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0002 :
    alphaDummy016 ∈
      (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv ∪
        ((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv)
        support_part_0002)
  have support_part_0003 : alphaDummy016 ∈ (((Class.cv alphaDummy016)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 :
    alphaDummy016 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy017)).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy017 ∈
      (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alphaDummy017 ∈
      (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv ∪
        ((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy016) (Class.cv alphaDummy017))).fv)
        support_part_0004)
  have support_part_0005 : alphaDummy017 ∈ (((Class.cv alphaDummy017)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0005 :
    alphaDummy017 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy016)).fv) support_part_0005)
  have support_part_0006 :
    alphaDummy016 ∈ (((synCcompl (Class.cv alphaDummy016))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0006 :
    alphaDummy016 ∈
      (((synCcompl (Class.cv alphaDummy016))).fv ∪
        ((synCcompl (Class.cv alphaDummy017))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy017))).fv) support_part_0006)
  have support_part_0007 : alphaDummy016 ∈ (((Class.cv alphaDummy016)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 :
    alphaDummy016 ∈
      (((Class.cv alphaDummy016)).fv ∪ ((Class.cv alphaDummy016)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy016)).fv) support_part_0007)
  have support_part_0008 :
    alphaDummy017 ∈ (((synCcompl (Class.cv alphaDummy017))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alphaDummy017 ∈
      (((synCcompl (Class.cv alphaDummy016))).fv ∪
        ((synCcompl (Class.cv alphaDummy017))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy016))).fv) support_part_0008)
  have support_part_0009 : alphaDummy017 ∈ (((Class.cv alphaDummy017)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0009 :
    alphaDummy017 ∈
      (((Class.cv alphaDummy017)).fv ∪ ((Class.cv alphaDummy017)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy017)).fv) support_part_0009)
  have support_part_0010 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    exact support_part_0010
  have support_part_0011 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0011 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    exact support_part_0011
  have splitAlpha0000 :
    TAlphaWff
      [(alphaDummy017, alphaDummy017), (alphaDummy016, alphaDummy016),
        (alphaDummy015, alphaDummy015), (alphaDummy008, alphaDummy008),
        (alphaDummy007, alphaDummy007), (alphaDummy010, alphaDummy010),
        (alphaDummy009, alphaDummy009), (alphaDummy000, x),
        (alphaDummy001, alphaDummy002), (alphaDummy004, alphaDummy006),
        (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy016) (Class.cv alphaDummy017))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy015)
            (synCun (Class.cv alphaDummy016) (Class.cv alphaDummy017)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy016) (Class.cv alphaDummy017))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy015)
            (synCun (Class.cv alphaDummy016) (Class.cv alphaDummy017))))) :=
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
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
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
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
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
              (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.there
                (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                  (by decide))
                (freshVar_injective (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
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
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
                                    (by decide)) (freshVar_injective
                                    (((Class.cv alphaDummy008)).fv ∪ ((synC1c)).fv)
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
    TAlphaWff
      [(alphaDummy000, x), (alphaDummy001, alphaDummy002),
        (alphaDummy004, alphaDummy006), (alphaDummy003, alphaDummy005)]
      (Wff.imp (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
        (Wff.neg (Wff.classMem A (Class.cv alphaDummy000))))
      (Wff.imp (Wff.classMem (Class.cv x) (synCnnc))
        (Wff.neg (Wff.classMem A (Class.cv x)))) :=
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
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (Nat.ne_of_lt
        (mem_lt_freshVar support_mem_0000 0)) (TAlphaVar.here _ _ _))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                        (TAlphaWff.ex (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
        (freshVar_injective ((∅ : Finset Var)) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
        (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0)) (TAlphaVar.here _ _ _)))))))))
                                    (TAlphaWff.neg splitAlpha0000)))))) (TAlphaClass.cv
                            (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (freshVar_injective ((∅ : Finset Var)) (by decide))
                              (TAlphaVar.here _ _ _))))))))) (TAlphaWff.objMem (TAlphaVar.there
                  (freshVar_injective (((Class.cab alphaDummy007
                        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy007))
                          (synWral alphaDummy008 (Class.cv alphaDummy007)
                            (Wff.classMem (synCplc (Class.cv alphaDummy008) (synC1c))
                              (Class.cv alphaDummy007)))))).fv) (by decide))
                  (freshVar_injective (((Class.cab alphaDummy007
                        (synWa (Wff.classMem (synC0c) (Class.cv alphaDummy007))
                          (synWral alphaDummy008 (Class.cv alphaDummy007)
                            (Wff.classMem (synCplc (Class.cv alphaDummy008) (synC1c))
                              (Class.cv alphaDummy007)))))).fv) (by decide))
                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.neg
        (TAlphaWff.classMem (TAlphaClass.reflOfFvFresh _ _ (by
              intro a b h hne;
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h;
              repeat'
                (first
                  | (rcases h with ⟨rfl, rfl⟩));
                all_goals aesop)) (TAlphaClass.cv (TAlphaVar.here _ _ _)))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy001 (Wff.classEq
                        (Class.cab alphaDummy000
                          (synWa (Wff.classMem (Class.cv alphaDummy000) (synCnnc))
                            (Wff.classMem A (Class.cv alphaDummy000))))
                        (synCsn (Class.cv alphaDummy001))))).fv) (by decide))
                (freshVar_injective (((Class.cab alphaDummy002 (Wff.classEq (Class.cab x
                          (synWa (Wff.classMem (Class.cv x) (synCnnc))
                            (Wff.classMem A (Class.cv x))))
                        (synCsn (Class.cv alphaDummy002))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg splitAlpha0001))
                  (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                          (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
