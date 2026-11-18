/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularProjection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularCompletion
public import LeanPool.TuringConeRigidity.CohenForcing.QuotientDense

/-!
# Regular Projection
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularProjection
open Set CountableForcing ForcingProjection BooleanProjection RegularCompletion
universe u
variable {P : Type u} [Preorder P]

/-- The forcing projection from original conditions to the positive part of a
complement-closed complete sublattice. -/
noncomputable def originalProjection (A : CompleteSublattice (Algebra P))
    (hc : ∀ a ∈ A, aᶜ ∈ A) : Projection P (PartPositive A) where
  map p := (forcingProjection A hc).map (positiveBasic p)
  mono := fun _ _ h => project_mono A (basic_mono h)
  lift := by
    intro p a hap
    obtain ⟨b,hbp,hba⟩ := (forcingProjection A hc).lift (positiveBasic p) a hap
    obtain ⟨q,hqp,hqb⟩ := refine_basic p b.val b.property hbp
    exact ⟨q,hqp,(project_mono A hqb).trans hba⟩

theorem originalProjection_dense (A : CompleteSublattice (Algebra P))
    (hc : ∀ a ∈ A, aᶜ ∈ A) : Dense (Set.range (originalProjection A hc).map) := by
  intro a
  obtain ⟨p,hpa⟩ := basic_dense a.val a.property.2
  exact ⟨(originalProjection A hc).map p,
    (project_le_iff A _ _ a.property.1).mpr hpa,p,rfl⟩

theorem originalProjection_countable_dense [Countable P]
    (A : CompleteSublattice (Algebra P)) (hc : ∀ a ∈ A, aᶜ ∈ A) :
    (Set.range (originalProjection A hc).map).Countable ∧
      Dense (Set.range (originalProjection A hc).map) :=
  ⟨Set.countable_range _,originalProjection_dense A hc⟩

theorem image_mem_iff (A : CompleteSublattice (Algebra P))
    (hc : ∀ a ∈ A, aᶜ ∈ A) (G : GenericFilter P) (a : PartPositive A) :
    a ∈ (imageFilter (originalProjection A hc) G).carrier ↔
      ∃ p ∈ G.carrier, p ∈ (a.val : LowerSet P) := by
  change (∃ p ∈ G.carrier, project A (basic p) ≤ a.val) ↔ _
  simp only [project_le_iff A _ _ a.property.1,basic_le_iff]

theorem countable_quotient_presentation [Countable P]
    (A : CompleteSublattice (Algebra P)) (hc : ∀ a ∈ A, aᶜ ∈ A)
    (H : GenericFilter (PartPositive A)) (D : Set P) (hD : Dense D)
    (hH : ∀ p, ∃ a ∈ H.carrier,
      a ∈ QuotientDense.requirement (originalProjection A hc) D p) :
    Countable (QuotientConditions (originalProjection A hc) H) ∧
      (∀ p, Dense (QuotientDense.requirement (originalProjection A hc) D p)) ∧
      Dense (QuotientDense.restriction (originalProjection A hc) H D) :=
  ⟨QuotientDense.quotient_countable _ _,
    QuotientDense.requirement_dense _ _ hD,QuotientDense.restriction_dense _ _ _ hH⟩

end TuringRigidity.RegularProjection

end OAI
