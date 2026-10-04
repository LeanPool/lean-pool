/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001009Uni. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_uni`. -/
@[expose]
noncomputable def nominalDfUni (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCuni A)
        (.cab x (synWex y (synWa (.objMem x y) (.classMem (.cv y) A))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((A).fv) 0)
  let alphaDummy001 : Var := (freshVar ((A).fv) 1)
  have fresh_000 : alphaDummy000 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 0
  have fresh_001 : alphaDummy001 ∉ ((A).fv) := by exact freshVar_not_mem ((A).fv) 1
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
              (TAlphaVar.there (freshVar_injective ((A).fv) (by decide)) dv_x_y
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    ((rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
