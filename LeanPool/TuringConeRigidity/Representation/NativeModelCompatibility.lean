/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/NativeModelCompatibility.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CountableSetReal
public import LeanPool.TuringConeRigidity.SetModels.PresentationGraphSet
public import LeanPool.TuringConeRigidity.SetModels.SetDegreeDecoding
public import LeanPool.TuringConeRigidity.SetModels.SetModelCountability

/-!
# Native Model Compatibility
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel SetModelReals SetDegreeDecoding PersistentRestrictions
  PersistentPresentation
universe u

theorem realCode_eq_realSet (A : Oracle) : realCode.{u} A = realSet A := rfl

theorem modelReals_eq_reals (M : ZFSet.{u}) : modelReals M = reals M := rfl

theorem native_countability_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    SetModelCountability.InternallyCountable M a ↔ InternallyCountable M a := by
  unfold SetModelCountability.InternallyCountable InternallyCountable
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  have he : ∀ i, cons f (cons ZFSet.omega (fun _ => a)) i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hf
    · exact sourceT_omega_mem M hM hT
    · exact ha
  rw [Formula.absolute _ M hM _ he,SetModelCountability.eval_ontoFormula]
  rfl

theorem degreeCode_eq_degreeSet (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode S A = degreeSet (degree A) := by
  apply ZFSet.ext; intro x
  rw [degreeCode,ZFSet.mem_sep,mem_degreeSet]
  constructor
  · rintro ⟨_,B,hB,hBA⟩
    exact ⟨B,hB,hBA⟩
  · rintro ⟨B,rfl,hBA⟩
    have hB := sourceT_real_lower M hM hT hA ((degree_eq_iff B A).mp hBA).1
    exact ⟨(hS B).mpr hB,B,rfl,hBA⟩

theorem presentationSet_eq_idealSet (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    {I : CountableIdeal} {H : Oracle} (hH : Presented I H) (hHM : H ∈ modelReals M) :
    presentationSet S H = idealSet I := by
  have eq (n : ℕ) := degreeCode_eq_degreeSet M hM hT S hS (sourceT_real_column M hM hT hHM n)
  apply ZFSet.ext; intro x
  rw [mem_presentationSet,mem_idealSet]
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨_,(hH _).mpr ⟨n,rfl⟩,eq n⟩
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨n,hn⟩ := (hH a).mp ha
    exact ⟨n,by rw [eq,hn]⟩

theorem presentationGraph_eq_automorphismSet (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    {I : CountableIdeal} {H : Oracle} (hH : Presented I H) (hHM : H ∈ modelReals M)
    (ρ : I ≃o I) (R : Oracle) (hR : ∀ v, R v = true ↔ Graph ρ hH v) :
    presentationGraph S H R = automorphismSet ρ := by
  have eq (n : ℕ) := degreeCode_eq_degreeSet M hM hT S hS (sourceT_real_column M hM hT hHM n)
  apply ZFSet.ext; intro z
  rw [mem_presentationGraph,mem_automorphismSet]
  constructor
  · rintro ⟨n,m,rfl,hr⟩
    have hg := (hR (Nat.pair n m)).mp hr
    simp only [PersistentPresentation.Graph,Nat.unpair_pair] at hg
    refine ⟨entry hH n,?_⟩
    rw [eq n,eq m,hg]
    rfl
  · rintro ⟨b,rfl⟩
    obtain ⟨n,hn⟩ := (hH b.val).mp b.property
    obtain ⟨m,hm⟩ := (hH (ρ b).val).mp (ρ b).property
    have hb : entry hH n = b := Subtype.ext hn
    refine ⟨n,m,?_,(hR (Nat.pair n m)).mpr ?_⟩
    · rw [eq n,eq m,hn,hm]
    · simp only [PersistentPresentation.Graph,Nat.unpair_pair,hb,hm]

end TuringRigidity.BoundedSetTheory

end OAI
