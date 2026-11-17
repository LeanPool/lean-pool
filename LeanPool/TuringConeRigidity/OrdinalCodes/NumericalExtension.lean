/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericalExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalIdeal

/-!
# Numerical Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericalExtension
open EncodedForcing PersistentRestrictions PersistentPresentation NumericalAutomorphism
noncomputable section

def Compatible (A H : Oracle) (R P : ℕ → Prop) : Prop :=
  ∀ i j n m, R (Nat.pair i j) → P (Nat.pair n m) →
    degree (columns A i) = degree (columns H n) →
    degree (columns A j) = degree (columns H m)

theorem compatible_iff {I J : CountableIdeal} {A H : Oracle}
    (hA : Presented I A) (hH : Presented J H) (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o I) (σ : J ≃o J) :
    Compatible A H (Graph ρ hA) (Graph σ hH) ↔ Extends hIJ ρ σ := by
  constructor
  · intro hc x
    obtain ⟨i,hi⟩ := (hA x.val).mp x.property
    obtain ⟨j,hj⟩ := (hA (ρ x).val).mp (ρ x).property
    obtain ⟨n,hn⟩ := (hH x.val).mp (hIJ x.property)
    obtain ⟨m,hm⟩ := (hH (σ ⟨x.val,hIJ x.property⟩).val).mp (σ ⟨x.val,hIJ x.property⟩).property
    have heI : entry hA i = x := Subtype.ext hi
    have heJ : entry hH n = ⟨x.val,hIJ x.property⟩ := Subtype.ext hn
    have hR : Graph ρ hA (Nat.pair i j) := by
      simp only [PersistentPresentation.Graph,Nat.unpair_pair]
      rw [heI,hj]
    have hP : Graph σ hH (Nat.pair n m) := by
      simp only [PersistentPresentation.Graph,Nat.unpair_pair]
      rw [heJ,hm]
    exact hm.symm.trans ((hc i j n m hR hP (hi.trans hn.symm)).symm.trans hj)
  · intro he i j n m hR hP hin
    have hi : (⟨(entry hA i).val,hIJ (entry hA i).property⟩ : J) = entry hH n := Subtype.ext hin
    have hh := he (entry hA i)
    rw [hi] at hh
    simp only [PersistentPresentation.Graph,Nat.unpair_pair] at hR hP
    exact hR.symm.trans (hh.symm.trans hP)

theorem compatible_congr {A H : Oracle} {R P Q : ℕ → Prop}
    (h : ∀ v, P v ↔ Q v) : Compatible A H R P ↔ Compatible A H R Q := by
  constructor
  · intro hc i j n m hR hQ
    exact hc i j n m hR ((h _).mpr hQ)
  · intro hc i j n m hR hP
    exact hc i j n m hR ((h _).mp hP)

end
end TuringRigidity.NumericalExtension

end OAI
