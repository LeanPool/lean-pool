/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001007Pw. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_pw`. -/
@[expose]
noncomputable def nominalDfPw (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCpw A) (.cab x (synWss (.cv x) A))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var :=
    (freshVar (((synCnin (Class.cv alphaDummy000) A)).fv ∪
        ((synCnin (Class.cv alphaDummy000) A)).fv) 0)
  let alphaDummy002 : Var :=
    (freshVar (((synCnin (Class.cv x) A)).fv ∪ ((synCnin (Class.cv x) A)).fv) 0)
  let alphaDummy003 : Var := (freshVar (((Class.cv alphaDummy000)).fv ∪ (A).fv) 0)
  let alphaDummy004 : Var := (freshVar (((Class.cv x)).fv ∪ (A).fv) 0)
  have fresh_000 : alphaDummy003 ∉ (((Class.cv alphaDummy000)).fv ∪ (A).fv) := by
    exact freshVar_not_mem (((Class.cv alphaDummy000)).fv ∪ (A).fv) 0
  have fresh_001 : alphaDummy004 ∉ (((Class.cv x)).fv ∪ (A).fv) := by
    exact freshVar_not_mem (((Class.cv x)).fv ∪ (A).fv) 0
  have fresh_002 :
    alphaDummy001 ∉
      (((synCnin (Class.cv alphaDummy000) A)).fv ∪
        ((synCnin (Class.cv alphaDummy000) A)).fv) :=
    by
    exact
      freshVar_not_mem
        (((synCnin (Class.cv alphaDummy000) A)).fv ∪
          ((synCnin (Class.cv alphaDummy000) A)).fv)
        0
  have fresh_003 :
    alphaDummy002 ∉ (((synCnin (Class.cv x) A)).fv ∪ ((synCnin (Class.cv x) A)).fv) :=
    by
    exact
      freshVar_not_mem (((synCnin (Class.cv x) A)).fv ∪ ((synCnin (Class.cv x) A)).fv) 0
  have fresh_004 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have support_part_0000 :
    alphaDummy000 ∈ (((synCnin (Class.cv alphaDummy000) A)).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0000 :
    alphaDummy000 ∈
      (((synCnin (Class.cv alphaDummy000) A)).fv ∪
        ((synCnin (Class.cv alphaDummy000) A)).fv) :=
    by
    exact
      (Finset.mem_union_left (((synCnin (Class.cv alphaDummy000) A)).fv) support_part_0000)
  have support_part_0001 : x ∈ (((synCnin (Class.cv x) A)).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0001 :
    x ∈ (((synCnin (Class.cv x) A)).fv ∪ ((synCnin (Class.cv x) A)).fv) := by
    exact (Finset.mem_union_left (((synCnin (Class.cv x) A)).fv) support_part_0001)
  have support_part_0002 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv ∪ (A).fv) :=
    by exact (Finset.mem_union_left ((A).fv) support_part_0002)
  have support_part_0003 : x ∈ (((Class.cv x)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0003 : x ∈ (((Class.cv x)).fv ∪ (A).fv) := by
    exact (Finset.mem_union_left ((A).fv) support_part_0003)
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfFvFresh _ _ (by
                              intro a b h hne;
                              simp only [List.mem_cons, List.not_mem_nil, or_false,
                                Prod.mk.injEq] at h;
                              repeat'
                                (first
                                  | (rcases h with ⟨rfl, rfl⟩));
                                all_goals aesop)))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0002 0))
                              (Nat.ne_of_lt (mem_lt_freshVar support_mem_0003 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                                (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                                (TAlphaVar.here _ _ _)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.reflOfFvFresh _ _ (by
                              intro a b h hne;
                              simp only [List.mem_cons, List.not_mem_nil, or_false,
                                Prod.mk.injEq] at h;
                              repeat'
                                (first
                                  | (rcases h with ⟨rfl, rfl⟩));
                                all_goals aesop))))))))))
          (TAlphaClass.cv (TAlphaVar.here _ _ _))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
