/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001004Csb. -/


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
noncomputable def nominal_df_csb (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_csb A x B) (.cab y (syn_wsbc A x (.classMem (.cv y) B)))) :=
  by
  let alpha_dummy_000 : Var := (freshVar ((A).fv ∪ ({ x } : Finset Var) ∪ (B).fv) 0)
  have fresh_000 : alpha_dummy_000 ∉ ((A).fv ∪ ({ x } : Finset Var) ∪ (B).fv) := by
    exact freshVar_not_mem ((A).fv ∪ ({ x } : Finset Var) ∪ (B).fv) 0
  have support_part_0000 : x ∈ (({ x } : Finset Var)) := by
    exact Finset.mem_singleton_self _
  have support_mem_0000 : x ∈ ((A).fv ∪ ({ x } : Finset Var) ∪ (B).fv) := by
    exact
      (Finset.mem_union_left ((B).fv) (Finset.mem_union_right ((A).fv) support_part_0000))
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.refl_of_fv_fresh _ _ (by
              intro a b h hne;
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h;
              repeat'
                (first
                  | (rcases h with ⟨rfl, rfl⟩));
                all_goals aesop)) (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cv
                (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0)))
                  (Ne.symm dv_x_y) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_fv_fresh _ _
                (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    (first
                      | (rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
