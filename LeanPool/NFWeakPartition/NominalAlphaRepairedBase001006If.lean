/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001006If. -/


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

/-- Checked nominal proof certificate identified upstream as `nominal_df_if`. -/
@[expose]
noncomputable def nominalDfIf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf
      (.classEq (synCif ph A B) (.cab x (synWo (synWa (.classMem (.cv x) A) ph)
            (synWa (.classMem (.cv x) B) (.neg ph))))) :=
  by
  let alphaDummy000 : Var := (freshVar ((ph).fv ∪ (A).fv ∪ (B).fv) 0)
  have fresh_000 : alphaDummy000 ∉ ((ph).fv ∪ (A).fv ∪ (B).fv) := by
    exact freshVar_not_mem ((ph).fv ∪ (A).fv ∪ (B).fv) 0
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfFvFresh _ _ (by
                    intro a b h hne;
                    simp only [List.mem_cons, List.not_mem_nil, or_false,
                      Prod.mk.injEq] at h;
                    repeat'
                      ((rcases h with ⟨rfl, rfl⟩));
                      all_goals aesop))) (TAlphaWff.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    ((rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop)))) (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    ((rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))) (TAlphaWff.neg (TAlphaWff.reflOfFvFresh _ _ (by
                  intro a b h hne;
                  simp only [List.mem_cons, List.not_mem_nil, or_false,
                    Prod.mk.injEq] at h;
                  repeat'
                    ((rcases h with ⟨rfl, rfl⟩));
                    all_goals aesop))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
