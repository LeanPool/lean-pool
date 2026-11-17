/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/PresentationEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelPresentationSets

/-!
# Presentation Enumeration
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing
universe u

noncomputable def presentationEnumeration (R : ZFSet.{u}) (H : Oracle) : ZFSet.{u} :=
  ZFSet.range (fun n : ℕ => ZFSet.pair (natSet n) (degreeCode R (columns H n)))

theorem mem_presentationEnumeration (R : ZFSet.{u}) (H : Oracle) (z : ZFSet.{u}) :
    z ∈ presentationEnumeration R H ↔ ∃ n, z = ZFSet.pair (natSet n) (degreeCode R (columns H n))
      := by
  rw [presentationEnumeration,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

theorem presentationEnumeration_pair (R : ZFSet.{u}) (H : Oracle) (n : ℕ) (D : ZFSet.{u}) :
    ZFSet.pair (natSet n) D ∈ presentationEnumeration R H ↔ D = degreeCode R (columns H n) := by
  rw [mem_presentationEnumeration]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨hn,hd⟩ := ZFSet.pair_inj.mp hi
    have he := natSet_injective hn
    subst i; exact hd
  · intro h; exact ⟨n,congrArg (ZFSet.pair (natSet n)) h⟩

theorem presentationEnumeration_function (R : ZFSet.{u}) (H : Oracle) :
    TransitiveNameModel.FunctionGraph ZFSet.omega (presentationSet R H) (presentationEnumeration R
      H) := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_presentationEnumeration R H z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,_,(mem_presentationSet R H _).mpr ⟨n,rfl⟩,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨_,(mem_presentationSet R H _).mpr ⟨n,rfl⟩,
      (presentationEnumeration_pair R H n _).mpr rfl,
      fun y _ hy => (presentationEnumeration_pair R H n y).mp hy⟩

theorem presentationEnumeration_onto (R : ZFSet.{u}) (H : Oracle) :
    ∀ D ∈ presentationSet R H, ∃ x ∈ ZFSet.omega, ZFSet.pair x D ∈ presentationEnumeration R H := by
  intro D hD
  obtain ⟨n,rfl⟩ := (mem_presentationSet R H D).mp hD
  exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,(presentationEnumeration_pair R H n _).mpr rfl⟩

namespace Formula
def presentationValue (φ : Formula) (o Q z R H n D : ℕ) : Formula :=
  .existsMem R (.conj (columnSet (o+1) (Q+1) (n+1) (H+1) 0)
    (degreeSet φ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)))

theorem presentationValue_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R H n D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : e H = realCode A) (N : ℕ) (hn : e n = natSet N)
    (hc : realCode (columns A N) ∈ e R) :
    (presentationValue φ o Q z R H n D).Eval e ↔ e D = degreeCode (e R) (columns A N) := by
  simp only [presentationValue,Formula.Eval]
  constructor
  · rintro ⟨B,_,hb,hd⟩
    have heB := (columnSet_spec (o+1) (Q+1) (n+1) (H+1) 0 (cons B e) ho hQ A hA N hn).mp hb
    exact (degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1) (cons B e)
      ho hQ hz hR (columns A N) heB).mp hd
  · intro hd
    refine ⟨realCode (columns A N),hc,?_,?_⟩
    · exact (columnSet_spec (o+1) (Q+1) (n+1) (H+1) 0 (cons (realCode (columns A N)) e)
        ho hQ A hA N hn).mpr rfl
    · exact (degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
        (cons (realCode (columns A N)) e) ho hQ hz hR (columns A N) rfl).mpr hd

def enumerationMember (φ : Formula) (o Q z R H I Z : ℕ) : Formula :=
  .existsMem o (.existsMem (I+1) (.conj (.orderedPair (Z+2) 1 0)
    (presentationValue φ (o+2) (Q+2) (z+2) (R+2) (H+2) 1 0)))

theorem enumerationMember_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R H I Z : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : e H = realCode A) (hc : ∀ n, realCode (columns A n) ∈ e R)
    (hI : e I = presentationSet (e R) A) :
    (enumerationMember φ o Q z R H I Z).Eval e ↔ e Z ∈ presentationEnumeration (e R) A := by
  simp only [enumerationMember,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  rw [ho,mem_presentationEnumeration]
  constructor
  · rintro ⟨n,hn,D,_,hp,hv⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have hd := (presentationValue_spec hφ (o+2) (Q+2) (z+2) (R+2) (H+2) 1 0
      (cons D (cons (natSet n) e)) ho hQ hz hR A hA n rfl (hc n)).mp hv
    exact ⟨n,hd ▸ hp⟩
  · rintro ⟨n,hp⟩
    refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,degreeCode (e R) (columns A n),?_,hp,?_⟩
    · rw [hI]; exact (mem_presentationSet _ _ _).mpr ⟨n,rfl⟩
    · exact (presentationValue_spec hφ (o+2) (Q+2) (z+2) (R+2) (H+2) 1 0
        (cons (degreeCode (e R) (columns A n)) (cons (natSet n) e)) ho hQ hz hR A hA n rfl (hc
          n)).mpr rfl
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
