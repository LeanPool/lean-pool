/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanProjection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRegularOrder
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanSyntax

/-!
# Internal Boolean Projection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanProjection
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax

/-- The members of `B` that are regular complements of members of `F`. -/
noncomputable def complements (c B F : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun V => ∃ U ∈ F, V = neg c U)

theorem complements_mem (M c B F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hF : F ∈ M) : complements c B F ∈ M := by
  let e := cons c (fun _ => F)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hc
    · exact hF
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 2 (negFormula 2 0 1)) e he hB
  simpa only [complements,Formula.Eval,negFormula_spec,cons_zero,cons_succ,e] using hs

theorem inf_eq_neg_sup (c B F : ZFSet.{0})
    (hB : ∀ U ∈ B, IsCode c U) (hF : F ⊆ B)
    (hN : ∀ U ∈ F, neg c U ∈ B) :
    infCode c F = neg c (supCode c (complements c B F)) := by
  have hFc := fun U hU => hB U (hF hU)
  have hNc : ∀ V ∈ complements c B F, IsCode c V :=
    fun V hV => hB V (ZFSet.mem_sep.mp hV).1
  have hI := inf_isCode c F hFc
  have hni : supCode c (complements c B F) ⊆ neg c (infCode c F) := by
    apply (supCode_le_iff c _ _ hNc (neg_isCode c _ hI)).mpr
    intro V hV
    obtain ⟨_,U,hU,rfl⟩ := ZFSet.mem_sep.mp hV
    exact neg_antitone c _ U (inf_subset c F hU)
  apply ZFSet.ext
  intro p
  constructor
  · intro hp
    apply neg_antitone c _ _ hni
    change p ∈ regular c (infCode c F)
    rwa [hI.2]
  · intro hp
    refine ZFSet.mem_sep.mpr ⟨neg_subset c _ hp,fun U hU => ?_⟩
    have hnU : neg c U ∈ complements c B F :=
      ZFSet.mem_sep.mpr ⟨hN U hU,U,hU,rfl⟩
    have hx := neg_antitone c _ _ (subset_supCode c _ hNc hnU) hp
    change p ∈ regular c U at hx
    rwa [(hFc U hU).2] at hx

theorem closed_inf (M c B Q A F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hA : Closed c B Q A) (hFM : F ∈ M) (hFA : F ⊆ A) : infCode c F ∈ A := by
  have hFB : F ⊆ B := fun _ h => hA.1 (hFA h)
  have hNF : complements c B F ⊆ A := by
    intro V hV
    obtain ⟨_,U,hU,rfl⟩ := ZFSet.mem_sep.mp hV
    exact hA.2.1 U (hFA hU)
  have hNQ : complements c B F ∈ Q := (hQ _).mpr
    ⟨complements_mem M c B F hM hT hc hBM hFM,fun _ h => (ZFSet.mem_sep.mp h).1⟩
  rw [inf_eq_neg_sup c B F (fun U hU => ((hB U).mp hU).2) hFB
    (fun U hU => hA.1 (hA.2.1 U (hFA hU)))]
  exact hA.2.1 _ (hA.2.2 _ hNQ hNF)

/-- The members of `A` containing `U` as a subset. -/
noncomputable def uppers (A U : ZFSet.{0}) : ZFSet.{0} := A.sep (fun V => U ⊆ V)

/-- The meet of all Boolean codes in `A` that contain `U`. -/
noncomputable def project (c A U : ZFSet.{0}) : ZFSet.{0} := infCode c (uppers A U)

theorem uppers_mem (M A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) : uppers A U ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.subset 1 0) (fun _ => U) (fun _ => hU) hA
  simpa only [uppers,Formula.eval_subset,cons_zero,cons_succ] using hs

theorem project_internal (M c A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hA : A ∈ M) (hU : U ∈ M) : project c A U ∈ M :=
  inf_mem M c _ hM hT hc (uppers_mem M A U hM hT hA hU)

theorem project_mem_part (M c B Q A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M) (hUM : U ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A) : project c A U ∈ A :=
  closed_inf M c B Q A _ hM hT hc hBM hB hQ hA
    (uppers_mem M A U hM hT hAM hUM) (fun _ h => (ZFSet.mem_sep.mp h).1)

theorem subset_project (c A U : ZFSet.{0}) (hUc : U ⊆ c) : U ⊆ project c A U :=
  subset_inf c _ U hUc (fun _ h => (ZFSet.mem_sep.mp h).2)

theorem project_le_iff (c A U V : ZFSet.{0}) (hUc : U ⊆ c) (hV : V ∈ A) :
    project c A U ⊆ V ↔ U ⊆ V := by
  constructor
  · intro h p hp; exact h (subset_project c A U hUc hp)
  · intro h; exact inf_subset c _ (ZFSet.mem_sep.mpr ⟨hV,h⟩)

theorem project_fixed (c A U : ZFSet.{0}) (hUc : U ⊆ c) (hU : U ∈ A) : project c A U = U := by
  have h := (project_le_iff c A U U hUc hU).mpr (fun _ h => h)
  exact ZFSet.ext (fun p => ⟨fun hp => h hp,fun hp => subset_project c A U hUc hp⟩)

theorem project_nonempty (c A U : ZFSet.{0}) (hUc : U ⊆ c) (hU : U ≠ ∅) : project c A U ≠ ∅ := by
  intro hp
  apply hU
  apply ZFSet.ext
  intro p
  constructor
  · intro h
    have hx := subset_project c A U hUc h
    rw [hp] at hx
    exact hx
  · exact fun h => False.elim (ZFSet.notMem_empty p h)

end TuringRigidity.InternalBooleanProjection

end OAI
