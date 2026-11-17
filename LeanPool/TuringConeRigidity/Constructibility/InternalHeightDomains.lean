/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/InternalHeightDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.LargestOrdinalSyntax

/-!
# Internal Height Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ordinalCut_mem_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) : ordinalCut A ∈ M := by
  have hs := sep_mem M hM hS (ordinalFormula 0) (fun _ => A) (fun _ => hA) hA
  have heq : A.sep (fun x => (ordinalFormula 0).Eval (cons x (fun _ => A))) = ordinalCut A := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,mem_ordinalCut,eval_ordinalFormula,cons_zero]
  exact heq ▸ hs

theorem ordinalHeight_mem_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) (hAt : Transitive A) :
    (ordinalHeight A).toZFSet ∈ M := by
  rw [ordinalHeight_toZFSet A hAt]
  exact ordinalCut_mem_model M A hM hS hA

theorem internal_ordinal_downward (M : ZFSet.{u}) (hM : Transitive M)
    {a b : Ordinal.{u}} (hb : b.toZFSet ∈ M) (hab : a ≤ b) : a.toZFSet ∈ M := by
  rcases lt_or_eq_of_le hab with h|rfl
  · exact hM _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr h)
  · exact hb

theorem internal_difference_successor (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    (a-b+1).toZFSet ∈ M :=
  internal_ordinal_succ M hM hT _
    (internal_ordinal_downward M hM ha (Ordinal.sub_le_self a b))

theorem internal_domains_with_largest_ordinal (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) (γ : Ordinal.{u}) (hγ : γ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ ∀ a : Ordinal.{u}, a.toZFSet ∈ M → β ≤ a →
      let δ := a - ordinalHeight (seed R) + 1
      δ.toZFSet ∈ M ∧ γ ≤ δ ∧ a.toZFSet ∈ level R δ ∧
        ∀ e : ℕ → ZFSet.{u}, e 0 ∈ level R δ →
          (largestOrdinalSentence.Sat (level R δ : Set ZFSet) e ↔ e 0 = a.toZFSet) := by
  refine ⟨ordinalHeight (level R γ),ordinalHeight_mem_model M _ hM
    hT.separation.finitePrefix.bounded (level_mem M R hM hT hR γ hγ) (level_transitive R γ),?_⟩
  intro a ha hle
  rw [ordinalHeight_level] at hle
  have hoff : ordinalHeight (seed R) ≤ a := (show ordinalHeight (seed R) ≤ ordinalHeight (seed R)
    + γ from le_self_add).trans hle
  have hγδ : γ ≤ a - ordinalHeight (seed R) + 1 :=
    (Ordinal.le_sub_of_add_le hle).trans (le_of_lt (lt_add_one _))
  have hm := largest_ordinal_at_difference R a hoff
  refine ⟨internal_difference_successor M hM hT a _ ha,hγδ,hm.1,?_⟩
  intro e he
  exact largestOrdinalSentence_unique _ (level_transitive R _) a hm.1
    (fun b hb => (hm.2 b).mp hb) e he

end TuringRigidity.RelativeConstructible

end OAI
