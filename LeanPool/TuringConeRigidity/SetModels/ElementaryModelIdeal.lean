/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryModelIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementaryDegreeHull

/-!
# Elementary Model Ideal
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SetDegreeDecoding
  PersistentRestrictions OracleJump
universe u

theorem model_reals_countable (M : ZFSet.{u}) [Countable (Conditions M)] : (modelReals
  M).Countable := by
  have hc : (M : Set ZFSet.{u}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro x hx; exact label_surjective M hx
  apply (hc.image decodeReal).mono
  intro A hA
  exact ⟨realCode A,hA,decodeReal_realCode A⟩

noncomputable def modelIdeal (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT :
  SourceT M) :
    CountableIdeal where
  carrier := {b | ∃ A ∈ modelReals M, degree A = b}
  nonempty := ⟨degree FixedArithmetic.zero,FixedArithmetic.zero,sourceT_zero_real M hM hT,rfl⟩
  countable := (model_reals_countable M).image degree
  lower := by
    intro a b hab hb
    obtain ⟨A,rfl⟩ := degree_surjective a
    obtain ⟨B,hB,rfl⟩ := hb
    exact ⟨A,sourceT_real_lower M hM hT hB hab,rfl⟩
  join_mem := by
    rintro a b ⟨A,hA,rfl⟩ ⟨B,hB,rfl⟩
    exact ⟨TuringRigidity.join A B,sourceT_real_join M hM hT hA hB,rfl⟩

theorem modelIdeal_mem (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT :
  SourceT M)
    (b : Degree) : b ∈ (modelIdeal M hM hT).carrier ↔ ∃ A ∈ modelReals M, degree A = b := Iff.rfl

theorem modelIdeal_jump (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT :
  SourceT M) :
    IdealLocality.JumpClosed (PersistentLocality.ideal (modelIdeal M hM hT)) := by
  rintro b ⟨A,hA,rfl⟩
  exact ⟨jump A,sourceT_real_jump M hM hT hA,rfl⟩

theorem hull_degree_iff (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a)
    (hR : ambientRealSet ∈ hullSet a) (hQ : ambientGraphBound ∈ hullSet a) (b : Degree) :
    b ∈ (modelIdeal (collapsed (hullSet a)) (collapsed_transitive _) (collapsed_hull_sourceT
      a)).carrier ↔
      degreeSet b ∈ hullSet a := by
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact degreeSet_mem_hull a hω (hn 0) hR hQ ((collapsed_hull_reals a hn hω A).mp hA)
  · intro hb
    obtain ⟨A,hA,hAb⟩ := degree_representative_in_hull a b hb
    exact ⟨A,(collapsed_hull_reals a hn hω A).mpr hA,hAb⟩

theorem hull_ideal_invariant (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a)
    (hR : ambientRealSet ∈ hullSet a) (hQ : ambientGraphBound ∈ hullSet a)
    (π : Degree ≃o Degree) (hπ : globalGraph π ∈ hullSet a) :
    let I := modelIdeal (collapsed (hullSet a)) (collapsed_transitive _) (collapsed_hull_sourceT a)
    ∀ b ∈ I.carrier, π b ∈ I.carrier ∧ π.symm b ∈ I.carrier := by
  intro I b hb
  have hd := (hull_degree_iff a hn hω hR hQ b).mp hb
  have hi := image_degreeSet_mem_hull a π hπ b hd
  exact ⟨(hull_degree_iff a hn hω hR hQ _).mpr hi.1,(hull_degree_iff a hn hω hR hQ _).mpr hi.2⟩

end TuringRigidity.ElementaryModel

end OAI
