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

@[expose]
noncomputable def nominal_df_addc (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.classEq (syn_cplc A B) (.cab x (syn_wrex y A (syn_wrex z B
              (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv ∪ (B).fv) 0)
  let alpha_dummy_001 : Var := (freshVar ((A).fv ∪ (B).fv) 1)
  let alpha_dummy_002 : Var := (freshVar ((A).fv ∪ (B).fv) 2)
  let alpha_dummy_003 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_004 : Var :=
    (freshVar (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪
        ((syn_cnin (Class.cv y) (Class.cv z))).fv) 0)
  let alpha_dummy_005 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_006 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv z)).fv) 0)
  let alpha_dummy_007 : Var :=
    (freshVar (((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv ∪
        ((syn_cnin (syn_cvv) (syn_ccompl (syn_cvv)))).fv) 0)
  let alpha_dummy_008 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_ccompl (syn_cvv))).fv) 0)
  let alpha_dummy_009 : Var := (freshVar ((∅ : Finset Var)) 0)
  let alpha_dummy_010 : Var := (freshVar (((syn_cvv)).fv ∪ ((syn_cvv)).fv) 0)
  let alpha_dummy_011 : Var :=
    (freshVar (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_002))).fv) 0)
  let alpha_dummy_012 : Var :=
    (freshVar (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) 0)
  let alpha_dummy_013 : Var :=
    (freshVar (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_001)).fv) 0)
  let alpha_dummy_014 : Var := (freshVar (((Class.cv y)).fv ∪ ((Class.cv y)).fv) 0)
  let alpha_dummy_015 : Var :=
    (freshVar (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_002)).fv) 0)
  let alpha_dummy_016 : Var := (freshVar (((Class.cv z)).fv ∪ ((Class.cv z)).fv) 0)
  have fresh_013 : alpha_dummy_000 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 0
  have fresh_014 : alpha_dummy_001 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 1
  have fresh_015 : alpha_dummy_002 ∉ ((A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ (B).fv) 2
  have support_part_0000 :
    alpha_dummy_001 ∈
      (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0000 :
    alpha_dummy_001 ∈
      (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv)
        support_part_0000)
  have support_part_0001 : y ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0001 :
    y ∈
      (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_cnin (Class.cv y) (Class.cv z))).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_002)).fv) support_part_0002)
  have support_part_0003 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0003)
  have support_part_0004 :
    alpha_dummy_002 ∈
      (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) :=
    by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0004 :
    alpha_dummy_002 ∈
      (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv) :=
    by
    exact
      (Finset.mem_union_left
        (((syn_cnin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))).fv)
        support_part_0004)
  have support_part_0005 : z ∈ (((syn_cnin (Class.cv y) (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      or_true]
  have support_mem_0005 :
    z ∈
      (((syn_cnin (Class.cv y) (Class.cv z))).fv ∪ ((syn_cnin (Class.cv y) (Class.cv z))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_cnin (Class.cv y) (Class.cv z))).fv) support_part_0005)
  have support_part_0006 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0006 :
    alpha_dummy_002 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_002)).fv) :=
    by exact (Finset.mem_union_right (((Class.cv alpha_dummy_001)).fv) support_part_0006)
  have support_part_0007 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0007 : z ∈ (((Class.cv y)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_right (((Class.cv y)).fv) support_part_0007)
  have support_part_0008 :
    alpha_dummy_001 ∈ (((syn_ccompl (Class.cv alpha_dummy_001))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0008 :
    alpha_dummy_001 ∈
      (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_002))).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_ccompl (Class.cv alpha_dummy_002))).fv) support_part_0008)
  have support_part_0009 : y ∈ (((syn_ccompl (Class.cv y))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0009 :
    y ∈ (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) := by
    exact (Finset.mem_union_left (((syn_ccompl (Class.cv z))).fv) support_part_0009)
  have support_part_0010 : alpha_dummy_001 ∈ (((Class.cv alpha_dummy_001)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0010 :
    alpha_dummy_001 ∈
      (((Class.cv alpha_dummy_001)).fv ∪ ((Class.cv alpha_dummy_001)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_001)).fv) support_part_0010)
  have support_part_0011 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0011 : y ∈ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) := by
    exact (Finset.mem_union_left (((Class.cv y)).fv) support_part_0011)
  have support_part_0012 :
    alpha_dummy_002 ∈ (((syn_ccompl (Class.cv alpha_dummy_002))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0012 :
    alpha_dummy_002 ∈
      (((syn_ccompl (Class.cv alpha_dummy_001))).fv ∪
        ((syn_ccompl (Class.cv alpha_dummy_002))).fv) :=
    by
    exact
      (Finset.mem_union_right (((syn_ccompl (Class.cv alpha_dummy_001))).fv) support_part_0012)
  have support_part_0013 : z ∈ (((syn_ccompl (Class.cv z))).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, fv_syn_ccompl, eq_self]
  have support_mem_0013 :
    z ∈ (((syn_ccompl (Class.cv y))).fv ∪ ((syn_ccompl (Class.cv z))).fv) := by
    exact (Finset.mem_union_right (((syn_ccompl (Class.cv y))).fv) support_part_0013)
  have support_part_0014 : alpha_dummy_002 ∈ (((Class.cv alpha_dummy_002)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0014 :
    alpha_dummy_002 ∈
      (((Class.cv alpha_dummy_002)).fv ∪ ((Class.cv alpha_dummy_002)).fv) :=
    by exact (Finset.mem_union_left (((Class.cv alpha_dummy_002)).fv) support_part_0014)
  have support_part_0015 : z ∈ (((Class.cv z)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0015 : z ∈ (((Class.cv z)).fv ∪ ((Class.cv z)).fv) := by
    exact (Finset.mem_union_left (((Class.cv z)).fv) support_part_0015)
  have split_alpha_0000 :
    TAlphaWff [(alpha_dummy_002, z), (alpha_dummy_001, y), (alpha_dummy_000, x)]
      (Wff.imp (Wff.classEq (syn_cin (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv alpha_dummy_000)
            (syn_cun (Class.cv alpha_dummy_001) (Class.cv alpha_dummy_002)))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv y) (Class.cv z)) (syn_c0))
        (Wff.neg (Wff.classEq (Class.cv x) (syn_cun (Class.cv y) (Class.cv z))))) :=
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
              (TAlphaClass.refl_of_fv_fresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))) (TAlphaWff.ex (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.refl_of_fv_fresh _ _ (by
                      intro a b h hne;
                      simp only [List.mem_cons, List.not_mem_nil, or_false,
                        Prod.mk.injEq] at h;
                      repeat'
                        (first
                          | (rcases h with ⟨rfl, rfl⟩));
                        all_goals aesop))) (TAlphaWff.neg split_alpha_0000))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
