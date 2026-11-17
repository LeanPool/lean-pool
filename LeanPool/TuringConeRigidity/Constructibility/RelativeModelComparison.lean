/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelComparison.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelOrdinals

/-!
# Relative Model Comparison
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem relativeModel_eq_of_same_ordinals (M N R : ZFSet.{u})
    (hM : Transitive M) (hTM : SourceT M) (hRM : R ∈ M)
    (hN : Transitive N) (hTN : SourceT N) (hRN : R ∈ N)
    (hord : ∀ o : Ordinal.{u}, o.toZFSet ∈ M ↔ o.toZFSet ∈ N) :
    relativeModel M R = relativeModel N R := by
  apply ZFSet.ext; intro x
  rw [mem_relativeModel M R x hM hTM hRM,mem_relativeModel N R x hN hTN hRN]
  unfold InRelativeModel
  apply exists_congr; intro o
  exact and_congr (hord o) Iff.rfl

theorem relativeModel_countable (M R : ZFSet.{u}) [Countable (Conditions M)] :
    Countable (Conditions (relativeModel M R)) := by
  let _ : Countable M := Countable.of_equiv (Conditions M) (equivShrink M).symm
  let f : relativeModel M R → M := fun x => ⟨x.val,relativeModel_subset M R x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : M => z.val) h
  let _ : Countable (relativeModel M R) := Function.Injective.countable hf
  exact Countable.of_equiv (relativeModel M R) (equivShrink (relativeModel M R))

theorem ground_relativeModel_sourceT_iff_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) :
    SourceT (relativeModel M (groundReals M)) ↔ Choice (relativeModel M (groundReals M)) := by
  constructor
  · exact SourceT.choice
  · intro hAC
    have hR := groundReals_mem M hM hT
    obtain ⟨hS,hRep⟩ := ground_relativeModel_levy_schemas M hM hT
    exact ⟨relativeModel_extensionality M _ hM,relativeModel_empty_set M _ hM hT hR,
      relativeModel_pairing M _ hM hT hR,relativeModel_union M _ hM hT hR,
      relativeModel_power_set M _ hM hT hR,ground_relativeModel_infinity M hM hT,
      relativeModel_foundation M _ hM,hAC,hS,hRep⟩

end TuringRigidity.RelativeConstructible

end OAI
