/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OwnDegreeExtensionMeaning.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.HomogeneousDegreeExtension
public import LeanPool.TuringConeRigidity.Representation.AmbientExtensionBody

/-!
# Own Degree Extension Meaning
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory SetDegreeDecoding PersistentRestrictions
  SetModelSatisfaction
open RelativeConstructible FullSetForcing ElementaryModel
universe u

theorem own_degree_extension_iff (E : ZFSet.{0}) [Countable (Conditions E)]
    (hE : Transitive E) (hTE : SourceT E) (I : CountableIdeal) (ρ : I ≃o I) (f : ZFSet.{0}) :
    OwnDegreeExtension E (idealSet I) (automorphismSet ρ) f ↔
      ∃ hIJ : I.carrier ⊆ (modelIdeal E hE hTE).carrier,
        ∃ σ : modelIdeal E hE hTE ≃o modelIdeal E hE hTE,
          automorphismSet σ = f ∧ Extends hIJ ρ σ := by
  have hr : ∀ w ∈ groundReals E, ∃ A : Oracle, realCode A = w := by
    intro w hw
    exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
  have hD := internal_degreeUniverse E hE hTE _ (groundReals_mem E hE hTE) hr
  have hd := ownDegreeUniverse_eq_idealSet E hE hTE (groundReals E) (mem_groundReals E)
  have hl := ownDegreeOrder_actual E hE hTE (groundReals E) (mem_groundReals E)
  unfold OwnDegreeExtension
  rw [hd]
  constructor
  · rintro ⟨ha,hij,hext⟩
    have hij' := ideal_subset_iff.mp hij
    obtain ⟨σ,hσ⟩ := decode_action (ArithmeticTree.sourceContext E hE hTE) hl
      (modelIdeal E hE hTE) (hd ▸ hD) ha
    refine ⟨hij',σ,hσ,(extends_sets_iff hij' ρ σ).mp ?_⟩
    rwa [hσ]
  · rintro ⟨hij,σ,hσ,hext⟩
    rw [←hσ]
    exact ⟨action_satisfaction (ArithmeticTree.sourceContext E hE hTE) hl (hd ▸ hD) σ,
      ideal_subset hij,extends_sets hext⟩

end TuringRigidity.BoundedForcing

end OAI
