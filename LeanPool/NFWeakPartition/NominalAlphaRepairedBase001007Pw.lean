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

@[expose]
noncomputable def nominal_df_pw (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_cpw A) (.cab x (syn_wss (.cv x) A))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv) 0)
  let alpha_dummy_001 : Var :=
    (freshVar (((syn_cnin (Class.cv alpha_dummy_000) A)).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_000) A)).fv) 0)
  let alpha_dummy_002 : Var :=
    (freshVar (((syn_cnin (Class.cv x) A)).fv ∪ ((syn_cnin (Class.cv x) A)).fv) 0)
  let alpha_dummy_003 : Var := (freshVar (((Class.cv alpha_dummy_000)).fv ∪ (A).fv) 0)
  let alpha_dummy_004 : Var := (freshVar (((Class.cv x)).fv ∪ (A).fv) 0)
  have fresh_000 : alpha_dummy_003 ∉ (((Class.cv alpha_dummy_000)).fv ∪ (A).fv) := by
    exact freshVar_not_mem (((Class.cv alpha_dummy_000)).fv ∪ (A).fv) 0
  have fresh_001 : alpha_dummy_004 ∉ (((Class.cv x)).fv ∪ (A).fv) := by
    exact freshVar_not_mem (((Class.cv x)).fv ∪ (A).fv) 0
  have fresh_002 :
    alpha_dummy_001 ∉
      (((syn_cnin (Class.cv alpha_dummy_000) A)).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_000) A)).fv) :=
    by
    exact
      freshVar_not_mem
        (((syn_cnin (Class.cv alpha_dummy_000) A)).fv ∪
          ((syn_cnin (Class.cv alpha_dummy_000) A)).fv)
        0
  have fresh_003 :
    alpha_dummy_002 ∉ (((syn_cnin (Class.cv x) A)).fv ∪ ((syn_cnin (Class.cv x) A)).fv) :=
    by
    exact
      freshVar_not_mem (((syn_cnin (Class.cv x) A)).fv ∪ ((syn_cnin (Class.cv x) A)).fv) 0
  have fresh_004 : alpha_dummy_000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have support_part_0000 :
    alpha_dummy_000 ∈ (((syn_cnin (Class.cv alpha_dummy_000) A)).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0000 :
    alpha_dummy_000 ∈
      (((syn_cnin (Class.cv alpha_dummy_000) A)).fv ∪
        ((syn_cnin (Class.cv alpha_dummy_000) A)).fv) :=
    by
    exact
      (Finset.mem_union_left (((syn_cnin (Class.cv alpha_dummy_000) A)).fv) support_part_0000)
  have support_part_0001 : x ∈ (((syn_cnin (Class.cv x) A)).fv) := by
    simp only [Finset.mem_singleton, Finset.mem_union, fv_class_cv, fv_syn_cnin, eq_self,
      true_or]
  have support_mem_0001 :
    x ∈ (((syn_cnin (Class.cv x) A)).fv ∪ ((syn_cnin (Class.cv x) A)).fv) := by
    exact (Finset.mem_union_left (((syn_cnin (Class.cv x) A)).fv) support_part_0001)
  have support_part_0002 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0002 : alpha_dummy_000 ∈ (((Class.cv alpha_dummy_000)).fv ∪ (A).fv) :=
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
                          (TAlphaClass.refl_of_fv_fresh _ _ (by
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
                          (TAlphaClass.refl_of_fv_fresh _ _ (by
                              intro a b h hne;
                              simp only [List.mem_cons, List.not_mem_nil, or_false,
                                Prod.mk.injEq] at h;
                              repeat'
                                (first
                                  | (rcases h with ⟨rfl, rfl⟩));
                                all_goals aesop))))))))))
          (TAlphaClass.cv (TAlphaVar.here _ _ _))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
