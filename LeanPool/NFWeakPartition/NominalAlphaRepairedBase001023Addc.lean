/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001023Addc. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_addc`. -/
@[expose]
noncomputable def nominalDfAddc (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (synCplc A B) (.cab x (synWrex y A (synWrex z B
              (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
                (.classEq (.cv x) (synCun (.cv y) (.cv z)))))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alphaDummy002 : Var := (freshVar ((A).fv ∪ (B).fv) 2)
  let alphaDummy003 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv ∪
        ((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((synCnin (Class.cv y) (Class.cv z))).fv ∪
        ((synCnin (Class.cv y) (Class.cv z))).fv) 0)
  let alphaDummy005 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy006 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)
  let alphaDummy007 : Var :=
    (freshVar (((synCnin (synCvv) (synCcompl (synCvv)))).fv ∪
        ((synCnin (synCvv) (synCcompl (synCvv)))).fv) 0)
  let alphaDummy008 : Var := (freshVar (((synCvv)).fv ∪ ((synCcompl (synCvv))).fv) 0)
  let alphaDummy009 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alphaDummy010 : Var := (freshVar (((synCvv)).fv ∪ ((synCvv)).fv) 0)
  let alphaDummy011 : Var :=
    (freshVar (((synCcompl (Class.cv alphaDummy001))).fv ∪
        ((synCcompl (Class.cv alphaDummy002))).fv) 0)
  let alphaDummy012 : Var :=
    (freshVar (((synCcompl (Class.cv y))).fv ∪ ((synCcompl (Class.cv z))).fv) 0)
  let alphaDummy013 : Var :=
    (freshVar (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy001)).fv) 0)
  let alphaDummy014 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0)
  let alphaDummy015 : Var :=
    (freshVar (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy002)).fv) 0)
  let alphaDummy016 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv z)).fv) 0)
  have fresh_013 : alphaDummy000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_014 : alphaDummy001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have fresh_015 : alphaDummy002 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 2
  have support_part_0000 :
    alphaDummy001 ∈
      (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0000 :
    alphaDummy001 ∈
      (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv ∪
        ((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv)
        support_part_0000)
  have support_part_0001 : y ∈ (((synCnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0001 :
    y ∈
      (((synCnin (Class.cv y) (Class.cv z))).fv ∪ ((synCnin (Class.cv y) (Class.cv z))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (Class.cv y) (Class.cv z))).fv) support_part_0001)
  have support_part_0002 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy002)).fv) support_part_0002)
  have support_part_0003 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0003)
  have support_part_0004 :
    alphaDummy002 ∈
      (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alphaDummy002 ∈
      (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv ∪
        ((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((synCnin (Class.cv alphaDummy001) (Class.cv alphaDummy002))).fv)
        support_part_0004)
  have support_part_0005 : z ∈ (((synCnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0005 :
    z ∈
      (((synCnin (Class.cv y) (Class.cv z))).fv ∪ ((synCnin (Class.cv y) (Class.cv z))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (Class.cv y) (Class.cv z))).fv) support_part_0005)
  have support_part_0006 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alphaDummy001)).fv) support_part_0006)
  have support_part_0007 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_right (((Class.cv y)).fv) support_part_0007)
  have support_part_0008 :
    alphaDummy001 ∈ (((synCcompl (Class.cv alphaDummy001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alphaDummy001 ∈
      (((synCcompl (Class.cv alphaDummy001))).fv ∪
        ((synCcompl (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCcompl (Class.cv alphaDummy002))).fv) support_part_0008)
  have support_part_0009 : y ∈ (((synCcompl (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0009 :
    y ∈ (((synCcompl (Class.cv y))).fv ∪ ((synCcompl (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((synCcompl (Class.cv z))).fv) support_part_0009)
  have support_part_0010 : alphaDummy001 ∈ (((Class.cv alphaDummy001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 :
    alphaDummy001 ∈
      (((Class.cv alphaDummy001)).fv ∪ ((Class.cv alphaDummy001)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy001)).fv) support_part_0010)
  have support_part_0011 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0011 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
    exact (Finset.mem_union_left (((Class.cv y)).fv) support_part_0011)
  have support_part_0012 :
    alphaDummy002 ∈ (((synCcompl (Class.cv alphaDummy002))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0012 :
    alphaDummy002 ∈
      (((synCcompl (Class.cv alphaDummy001))).fv ∪
        ((synCcompl (Class.cv alphaDummy002))).fv) :=
    by
    exact
      (Finset.mem_union_right (((synCcompl (Class.cv alphaDummy001))).fv) support_part_0012)
  have support_part_0013 : z ∈ (((synCcompl (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0013 :
    z ∈ (((synCcompl (Class.cv y))).fv ∪ ((synCcompl (Class.cv z))).fv) := by
    exact (Finset.mem_union_right (((synCcompl (Class.cv y))).fv) support_part_0013)
  have support_part_0014 : alphaDummy002 ∈ (((Class.cv alphaDummy002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alphaDummy002 ∈
      (((Class.cv alphaDummy002)).fv ∪ ((Class.cv alphaDummy002)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alphaDummy002)).fv) support_part_0014)
  have support_part_0015 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0015 : z ∈ (((Class.cv z)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0015)
  have splitAlpha0000 :
    TAlphaWff [(alphaDummy002, z), (alphaDummy001, y), (alphaDummy000, x)]
      (Wff.imp (Wff.classEq (synCin (Class.cv alphaDummy001) (Class.cv alphaDummy002))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv alphaDummy000)
            (synCun (Class.cv alphaDummy001) (Class.cv alphaDummy002)))))
      (Wff.imp (Wff.classEq (synCin (Class.cv y) (Class.cv z)) (synC0))
        (Wff.neg (Wff.classEq (Class.cv x) (synCun (Class.cv y) (Class.cv z))))) :=
    (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.there
                                (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
                              (TAlphaVar.here _ _ _)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                              (TAlphaVar.there
                                (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_y_z
                                (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0006 0))
                            (Nat.ne_of_lt (mem_lt_freshVar support_mem_0007 0)) (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0004 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0005 0))
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
        (TAlphaWff.classEq (TAlphaClass.cv
            (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_z
              (TAlphaVar.there (freshVar_injective ((A).fv ∪ (B).fv) (by decide)) dv_x_y
                (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                  dv_y_z (TAlphaVar.here _ _ _))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0010 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0011 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0008 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0009 0))
                                (TAlphaVar.there
                                  (freshVar_injective ((A).fv ∪ (B).fv) (by decide))
                                  dv_y_z (TAlphaVar.here _ _ _))))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0014 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0015 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0012 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0013 0))
                                (TAlphaVar.here _ _ _)))))))))))))))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))) (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.reflOfFvFresh _ _ (by
                      intro a b h hne;
                      simp only [List.mem_cons, List.not_mem_nil, or_false,
                        Prod.mk.injEq] at h;
                      repeat'
                        (first
                          | (rcases h with ⟨rfl, rfl⟩));
                        all_goals aesop))) (TAlphaWff.neg splitAlpha0000))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
