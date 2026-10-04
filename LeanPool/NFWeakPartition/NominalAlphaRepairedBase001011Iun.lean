/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001011Iun. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_iun`. -/
@[expose]
noncomputable def nominalDfIun (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCiun x A B) (.cab y (synWrex x A (.classMem (.cv y) B)))) :=
  by
  let alphaDummy000 : Var := (freshVar (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0)
  have fresh_000 : alphaDummy000 ∉ (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) := by
    exact freshVar_not_mem (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) 0
  have support_part_0000 : x ∈ (({ x } : Finset Var)) := by
    exact Finset.mem_singleton_self _
  have support_mem_0000 : x ∈ (({ x } : Finset Var) ∪ (A).fv ∪ (B).fv) := by
    exact
      (Finset.mem_union_left ((B).fv) (Finset.mem_union_left ((A).fv) support_part_0000))
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
                    all_goals aesop))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                  (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
                  (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfFvFresh _ _
                (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
