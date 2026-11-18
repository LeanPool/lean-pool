/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/LevelInlinedDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.ConstructionStageBound
public import LeanPool.TuringConeRigidity.Constructibility.PersistentConstruction

/-!
# Level Inlined Definition
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SetModelArithmetic
open SetDegreeDecoding PersistentRestrictions
universe u

theorem Construction.singleInputs_relative (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (hi : t.Indexed M) :
    ∀ i, t.singleInputs (groundReals M) P i ∈ relativeModel M (groundReals M) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have hN := relativeModel_transitive M R hM
  have hp := relativeModel_pairing M R hM hT hR
  have hu := relativeModel_union M R hM hT hR
  have hpow := relativeModel_power_set M R hM hT hR
  have hs := relativeModel_bounded_separation M R hM hT hR
  have hinf := ground_relativeModel_infinity M hM hT
  have hw := ground_relativeModel_omega M hM hT
  intro i
  rcases i with _|_|_|_|_|i
  · exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
  · exact (relativeModel_ground_reals M hM hT (realCode P) (realCode_subset P)).mpr hP
  · exact hw
  · exact additionSet_mem N hN hp hu hpow hs hinf
  · exact product_mem N hN hp hu hpow hs hw hw
  · have hid := t.inputData_indexed M hi i
    change t.stageInputs R i ∈ N
    unfold Construction.stageInputs
    cases hd : t.inputData i with
    | reals => exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M R hM hT)
    | realPath path => exact (mem_relativeModel M R R hM hT hR).mpr (parameter_in_relativeModel M
      R hM hT)
    | stage o =>
      rw [hd] at hid
      exact (mem_relativeModel M R _ hM hT hR).mpr (level_in_relativeModel M R hM hT o hid)

theorem Construction.inlined_at_level (t : Construction.{u}) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (hP : P ∈ modelReals M) (ht : t.Certified (groundReals M) P) (hi : t.Indexed M) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      t.value (groundReals M) P ∈ level (groundReals M) γ ∧
      (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      ∀ z ∈ level (groundReals M) γ,
        t.singleMembership.Sat (level (groundReals M) γ : Set ZFSet)
          (cons z (t.singleInputs (groundReals M) P)) ↔ z ∈ t.value (groundReals M) P := by
  let R := groundReals M
  have hR := groundReals_mem M hM hT
  have hinputs := t.singleInputs_relative M hM hT P hP hi
  let e := cons (t.value R P) (t.singleInputs R P)
  have he (i : ℕ) (_hin : i < 6) : InRelativeModel M R (e i) := by
    cases i with
    | zero => exact t.value_in_relativeModel M R hM hT P ht hi
    | succ i => exact (mem_relativeModel M R _ hM hT hR).mp (hinputs i)
  obtain ⟨o,ho,hbound⟩ := finite_parameters_in_relative_level M R hM hT e 6 he
  let γ := max o t.stageBound
  have hγ : γ.toZFSet ∈ M := internal_ordinal_max M ho (t.stageBound_mem M hM hT hi)
  have hv : t.value R P ∈ level R γ := level_mono R (le_max_left _ _) (hbound 0 (by decide))
  have hin (i : ℕ) : t.singleInputs R P i ∈ level R γ := by
    by_cases hi5 : i < 5
    · exact level_mono R (le_max_left _ _) (hbound (i+1) (by omega))
    · obtain ⟨k,rfl⟩ : ∃ k, i = k+5 := ⟨i-5,by omega⟩
      change t.stageInputs R k ∈ level R γ
      exact level_mono R (le_max_right _ _) (t.stageInputs_bounded R k)
  refine ⟨γ,hγ,hv,hin,?_⟩
  intro z hz
  exact t.singleMembership_of_inputs (level R γ) R (level_transitive R γ) P ht hin hv z hz

theorem persistent_graph_inlined_at_level (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    ∃ (t : Construction.{u}) (P : Oracle) (γ : Ordinal.{u}),
      P ∈ modelReals M ∧ t.Indexed M ∧ t.Certified (groundReals M) P ∧
      γ.toZFSet ∈ M ∧ t.value (groundReals M) P = automorphismSet ρ ∧
      automorphismSet ρ ∈ level (groundReals M) γ ∧
      (∀ i, t.singleInputs (groundReals M) P i ∈ level (groundReals M) γ) ∧
      ∀ z ∈ level (groundReals M) γ,
        t.singleMembership.Sat (level (groundReals M) γ : Set ZFSet)
          (cons z (t.singleInputs (groundReals M) P)) ↔ z ∈ automorphismSet ρ := by
  obtain ⟨t,P,hP,hi,ht,hval⟩ := persistent_graph_construction M hM hT ρ hρ
  obtain ⟨γ,hγ,hv,he,hf⟩ := t.inlined_at_level M hM hT P hP ht hi
  refine ⟨t,P,γ,hP,hi,ht,hγ,hval,hval ▸ hv,he,?_⟩
  intro z hz
  rw [← hval]
  exact hf z hz

end TuringRigidity.RelativeConstructible

end OAI
