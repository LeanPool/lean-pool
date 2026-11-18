/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/LevelSubsetDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.LevelInlinedDefinition

/-!
# Level Subset Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions
universe u

theorem Construction.subset_at_level (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      t.value (groundReals M) P = definedSubset (level (groundReals M) γ) t.singleMembership
        (fun i : Fin t.singleMembership.bound => t.singleInputs (groundReals M) P i) := by
  obtain ⟨γ,hγ,hv,he,hf⟩ := t.inlined_at_level M hM hT P hP ht hi
  refine ⟨γ,hγ,he,?_⟩
  apply ZFSet.ext; intro z
  rw [mem_definedSubset]
  have hs := t.singleMembership.finite_support (level (groundReals M) γ : Set ZFSet)
    (cons z (t.singleInputs (groundReals M) P))
    (cons z (tupleEnv (fun i : Fin t.singleMembership.bound => t.singleInputs (groundReals M) P i)))
    (by
      intro i hin
      cases i with
      | zero => rfl
      | succ i =>
        simp only [cons_succ,tupleEnv,dite_eq_left (show i < t.singleMembership.bound by omega)])
  constructor
  · intro hz
    have hzL := level_transitive _ γ _ hv z hz
    exact ⟨hzL,hs.mp ((hf z hzL).mpr hz)⟩
  · rintro ⟨hzL,hz⟩
    exact (hf z hzL).mp (hs.mpr hz)

theorem persistent_extension_subset_at_level (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      Extends hIM ρ σ ∧ Persistent (modelIdeal M hM hT) σ ∧
      ∃ (t : Construction.{u}) (P : Oracle) (γ : Ordinal.{u}),
        P ∈ modelReals M ∧ t.Indexed M ∧ t.Certified (groundReals M) P ∧ γ.toZFSet ∈ M ∧
        (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
        automorphismSet σ = definedSubset (level (groundReals M) γ) t.singleMembership
          (fun i : Fin t.singleMembership.bound => t.singleInputs (groundReals M) P i) := by
  obtain ⟨σ,he,hσ,t,P,hP,hi,ht,hval⟩ := persistent_extension_construction M hM hT I ρ hρ hz hIM
  obtain ⟨γ,hγ,hin,hdef⟩ := t.subset_at_level M hM hT P hP ht hi
  exact ⟨σ,he,hσ,t,P,γ,hP,hi,ht,hγ,hin,hval ▸ hdef⟩

end TuringRigidity.RelativeConstructible

end OAI
