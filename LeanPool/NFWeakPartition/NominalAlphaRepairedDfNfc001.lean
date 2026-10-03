/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedDfNfc001. -/


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
noncomputable def nominal_df_nfc (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wnfc x A) (.all y (syn_wnf x (.classMem (.cv y) A)))) :=
  by
  let alpha_dummy_000 : Var := (freshVar (({ x } : Finset Var) ∪ (A).fv) 0)
  have fresh_000 : alpha_dummy_000 ∉ (({ x } : Finset Var) ∪ (A).fv) := by
    exact freshVar_not_mem (({ x } : Finset Var) ∪ (A).fv) 0
  have support_part_0000 : x ∈ (({ x } : Finset Var)) := by
    exact Finset.mem_singleton_self _
  have support_mem_0000 : x ∈ (({ x } : Finset Var) ∪ (A).fv) := by
    exact (Finset.mem_union_left ((A).fv) support_part_0000)
  change
    Nominal.NPrf
      (Wff.biimp (syn_wnfc x A) (Wff.all y (syn_wnf x (Wff.classMem (Class.cv y) A))))
  exact
    Nominal.alphaBiimp
      (TAlphaWff.all (TAlphaWff.all (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
                  (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_fv_fresh _ _
                (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))) (TAlphaWff.all (TAlphaWff.classMem (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
                    (Ne.symm dv_x_y) (TAlphaVar.there
                      (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
                      (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))))
                (TAlphaClass.refl_of_fv_fresh _ _ (by
                    intro a b h hne;
                    simp only [List.mem_cons, List.not_mem_nil, or_false,
                      Prod.mk.injEq] at h;
                    repeat'
                      (first
                        | (rcases h with ⟨rfl, rfl⟩));
                      all_goals aesop)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
