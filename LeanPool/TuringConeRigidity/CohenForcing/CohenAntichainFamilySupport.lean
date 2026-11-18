/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenAntichainFamilySupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenAntichainSelector
public import LeanPool.TuringConeRigidity.CohenForcing.CohenInternalSupport
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableUnion
public import LeanPool.TuringConeRigidity.SetModels.InternalSequenceRange

/-!
# Cohen Antichain Family Support
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenAntichainFamilySupport
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenAntichainStages
open InternalSequenceRange CohenInternalSupport

theorem antichain_union_counted (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ conditions A ∧ Anti (conditions A) (E n))
    (hB : orbitGraph E ∈ M) :
    ∃ F ∈ M, (∀ p, p ∈ F ↔ ∃ n, p ∈ E n) ∧ F ⊆ conditions A ∧
      (F = ∅ ∨ InternallyCountable M F) := by
  classical
  have hc := conditions_mem M A hM hT hA
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hEQ : ∀ n, E n ∈ Q := fun n => (hQ _).mpr ⟨(hE n).1,(hE n).2.1⟩
  let S := rangeSet Q (orbitGraph E)
  have hSM : S ∈ M := rangeSet_mem M Q _ hM hT hQM hB
  have hS (H : ZFSet.{0}) : H ∈ S ↔ ∃ n, H = E n := mem_rangeSet Q E hEQ H
  have hsub : ∀ H ∈ S, H ⊆ conditions A := by
    intro H hH
    obtain ⟨n,rfl⟩ := (hS H).mp hH
    exact (hE n).2.1
  let F := unionSet (conditions A) S
  have hFM : F ∈ M := unionSet_mem M _ S hM hT hc hSM
  have hF (p : ZFSet.{0}) : p ∈ F ↔ ∃ n, p ∈ E n := by
    rw [mem_unionSet _ _ _ hsub]
    exact ⟨fun ⟨H,hH,hp⟩ => by obtain ⟨n,rfl⟩ := (hS H).mp hH; exact ⟨n,hp⟩,
      fun ⟨n,hp⟩ => ⟨E n,(hS _).mpr ⟨n,rfl⟩,hp⟩⟩
  refine ⟨F,hFM,hF,fun _ h => (ZFSet.mem_sep.mp h).1,?_⟩
  by_cases hempty : F = ∅
  · exact Or.inl hempty
  · right
    apply InternalCountableUnion.internally_countable_union M F S hM hT hFM hSM
    · intro H hH p hp
      obtain ⟨n,rfl⟩ := (hS H).mp hH
      exact (hF p).mpr ⟨n,hp⟩
    · intro H hH
      obtain ⟨n,rfl⟩ := (hS H).mp hH
      exact CohenCountedAntichain.every_internal_antichain_counted M A (E n) hM hT hA
        (hE n).1 (hE n).2.1 (hE n).2.2
    · exact fun n => (hS _).mpr ⟨n,rfl⟩
    · exact hB
    · exact fun p hp => (hF p).mp hp
    · by_contra h
      apply hempty
      apply ZFSet.ext; intro p
      exact ⟨fun hp => False.elim (h ⟨p,hp⟩),fun hp => False.elim (ZFSet.notMem_empty p hp)⟩

theorem family_support_counted (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ conditions A ∧ Anti (conditions A) (E n))
    (hB : orbitGraph E ∈ M) :
    ∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ supportSet A p) ∧
      (S = ∅ ∨ InternallyCountable M S) := by
  obtain ⟨F,hFM,hF,hFc,hct⟩ := antichain_union_counted M A hM hT hA E hE hB
  refine ⟨used A F,used_mem M A F hM hT hA hFM,
    fun _ h => (ZFSet.mem_sep.mp h).1,?_,?_⟩
  · intro x
    simp only [used,ZFSet.mem_sep]
    constructor
    · rintro ⟨_,p,hp,hxp⟩
      obtain ⟨n,hp⟩ := (hF p).mp hp
      exact ⟨n,p,hp,hxp⟩
    · rintro ⟨n,p,hp,hxp⟩
      exact ⟨(ZFSet.mem_sep.mp hxp).1,p,(hF p).mpr ⟨n,hp⟩,hxp⟩
  · rcases hct with rfl|hct
    · left
      apply ZFSet.ext; intro x
      simp only [used,ZFSet.mem_sep,ZFSet.notMem_empty,false_and,exists_false,and_false]
    · exact used_counted M A F hM hT hA hFM hFc hct

theorem selected_family_support (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (U : ℕ → ZFSet.{0})
    (hU : ∀ n, U n ∈ M ∧ U n ⊆ conditions A) (hB : orbitGraph U ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      (∀ n, E n ∈ M ∧ CohenAntichainSelector.Selected (conditions A) (U n) (E n)) ∧
      ∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ supportSet A p) ∧
        (S = ∅ ∨ InternallyCountable M S) := by
  obtain ⟨E,hE,hsel⟩ := CohenAntichainSelector.internal_antichain_family M A hM hT hA U hU hB
  refine ⟨E,hE,fun n => ⟨(hsel n).1,(hsel n).2.1⟩,?_⟩
  exact family_support_counted M A hM hT hA E
    (fun n => ⟨(hsel n).1,fun _ h => (hU n).2 ((hsel n).2.1.1 h),(hsel n).2.1.2.1⟩) hE

end TuringRigidity.CohenAntichainFamilySupport

end OAI
