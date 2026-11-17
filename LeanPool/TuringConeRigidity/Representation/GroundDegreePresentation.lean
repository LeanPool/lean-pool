/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundDegreePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseExistence
public import LeanPool.TuringConeRigidity.SetModels.ModelIdealInterpretation

/-!
# Ground Degree Presentation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation OracleJump
universe u

theorem sourceT_zero_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    FixedArithmetic.zero ∈ modelReals M := by
  have he : realCode.{u} FixedArithmetic.zero = ∅ := by
    apply ZFSet.ext; intro x
    constructor
    · intro hx
      obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
      have hn := (natSet_mem_realCode FixedArithmetic.zero n).mp hx
      exact Bool.noConfusion hn
    · exact fun hx => False.elim (ZFSet.notMem_empty _ hx)
  change realCode FixedArithmetic.zero ∈ M
  rw [he]
  exact hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero

theorem degreeCode_in_universe_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    (A : Oracle) (hA : degreeCode S A ∈ degreeUniverse S) : A ∈ modelReals M := by
  obtain ⟨B,hB,_⟩ := degreeUniverse_nonempty_member S (degreeCode S A) hA
  obtain ⟨hBS,hBA⟩ := (realCode_mem_degreeCode S A B).mp hB
  have hAB : degree A ≤ degree B := le_of_eq hBA.symm
  exact sourceT_real_lower M hM hT ((hS B).mp hBS) hAB

theorem ground_degree_presentation (M N : ZFSet.{u})
    (hM : Transitive M) (hN : Transitive N) (hTM : SourceT M) (hTN : SourceT N)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    (hSd : ∀ x ∈ S, ∃ A : Oracle, realCode A = x)
    (hUN : degreeUniverse S ∈ N) (hcount : InternallyCountable N (degreeUniverse S)) :
    ∃ I : CountableIdeal, ∃ H ∈ modelReals N, Presented I H ∧
      presentationSet S H = degreeUniverse S ∧
      (∀ n, columns H n ∈ modelReals M) ∧
      (∀ a : Degree, a ∈ I.carrier ↔ ∃ A ∈ modelReals M, degree A = a) ∧
      degree (jump FixedArithmetic.zero) ∈ I.carrier ∧
      IdealLocality.JumpClosed (PersistentLocality.ideal I) := by
  obtain ⟨H,hHN,hHU⟩ := internal_countable_degree_presentation N hN hTN S hSd hUN (fun _ h => h)
    hcount
  have hcol (n : ℕ) : columns H n ∈ modelReals M :=
    degreeCode_in_universe_real M hM hTM S hS (columns H n)
      (hHU ▸ (mem_presentationSet S H _).mpr ⟨n,rfl⟩)
  have hc : ∀ n, realCode (columns H n) ∈ S := fun n => (hS _).mpr (hcol n)
  let C : Set Degree := Set.range (fun n => degree (columns H n))
  have hmem (A : Oracle) : degree A ∈ C ↔ A ∈ modelReals M := by
    constructor
    · rintro ⟨n,hn⟩
      exact sourceT_real_lower M hM hTM (hcol n) (le_of_eq hn.symm)
    · intro hAM
      have hAU : degreeCode S A ∈ degreeUniverse S := (mem_degreeUniverse S _).mpr ⟨A,(hS A).mpr
        hAM,rfl⟩
      exact (degreeCode_mem_presentationSet S H hc A).mp (hHU.symm ▸ hAU)
  have hlower : ∀ {a b : Degree}, a ≤ b → b ∈ C → a ∈ C := by
    intro a b hab hb
    obtain ⟨A,rfl⟩ := degree_surjective a
    obtain ⟨B,rfl⟩ := degree_surjective b
    exact (hmem A).mpr (sourceT_real_lower M hM hTM ((hmem B).mp hb) hab)
  have hjoin : ∀ {a b : Degree}, a ∈ C → b ∈ C → a ⊔ b ∈ C := by
    intro a b ha hb
    obtain ⟨A,rfl⟩ := degree_surjective a
    obtain ⟨B,rfl⟩ := degree_surjective b
    exact (hmem (TuringRigidity.join A B)).mpr
      (sourceT_real_join M hM hTM ((hmem A).mp ha) ((hmem B).mp hb))
  let I : CountableIdeal := ⟨C,⟨degree (columns H 0),0,rfl⟩,Set.countable_range _,@hlower,@hjoin⟩
  refine ⟨I,H,hHN,fun _ => Iff.rfl,hHU,hcol,?_,?_,?_⟩
  · intro a
    obtain ⟨A,rfl⟩ := degree_surjective a
    exact ⟨fun h => ⟨A,(hmem A).mp h,rfl⟩,
      fun ⟨B,hB,he⟩ => he ▸ (hmem B).mpr hB⟩
  · exact (hmem _).mpr (sourceT_real_jump M hM hTM (sourceT_zero_real M hM hTM))
  · intro a ha
    obtain ⟨A,rfl⟩ := degree_surjective a
    exact (hmem _).mpr (sourceT_real_jump M hM hTM ((hmem A).mp ha))

end TuringRigidity.BoundedSetTheory

end OAI
