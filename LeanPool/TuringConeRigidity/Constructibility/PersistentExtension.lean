/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistentExtension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentRestrictionCode
public import LeanPool.TuringConeRigidity.Constructibility.PersistentCountability

/-!
# Persistent Extension
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistentExtension
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation PersistentCountability
noncomputable section

theorem nonpersistent_witness {J : CountableIdeal} {σ : J ≃o J}
    (h : ¬ Persistent J σ) :
    ∃ x, ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier) (τ : K ≃o K),
      x ∈ K.carrier → ¬ Extends hJK σ τ := by
  simpa only [Persistent,not_forall,not_exists,not_and] using h

theorem source_4_1_10 (I J : CountableIdeal) (ρ : I ≃o I)
    (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hj : JumpClosed (ideal J)) :
    ∃ σ : J ≃o J, Extends hIJ ρ σ ∧ Persistent J σ := by
  classical
  by_contra hn
  have hnot (σ : J ≃o J) (he : Extends hIJ ρ σ) : ¬ Persistent J σ :=
    fun hpσ => hn ⟨σ,he,hpσ⟩
  obtain ⟨H,hpres⟩ := presentation_exists J
  let S : Set (J ≃o J) := {σ | RecursivePred (iterate H 11) (Graph σ hpres)}
  have hS : S.Countable := arithmetic_maps_countable hpres _
  have : Countable S := hS.to_subtype
  have hwitness (σ : S) : ∃ x, Extends hIJ ρ σ.val →
      ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier) (τ : K ≃o K),
        x ∈ K.carrier → ¬ Extends hJK σ.val τ := by
    by_cases he : Extends hIJ ρ σ.val
    · obtain ⟨x,hx⟩ := nonpersistent_witness (hnot σ.val he)
      exact ⟨x,fun _ => hx⟩
    · exact ⟨⊥,fun h => (he h).elim⟩
  choose w hw using hwitness
  let L := JumpIdeal.generated (degree H)
  have hJL : J.carrier ⊆ L.carrier := by
    intro x hx
    obtain ⟨n,rfl⟩ := (hpres x).mp hx
    exact L.lower (CodingExtraction.column_projection_reduces H n) (JumpIdeal.includes _)
  obtain ⟨b,hb⟩ := CountableBound.countable_bounded (Set.range w ∪ L.carrier)
    ((Set.countable_range w).union L.countable)
  obtain ⟨K,hIK,τ,hbK,he⟩ := hp b
  have hLK : L.carrier ⊆ K.carrier := fun x hx => K.lower (hb x (Or.inr hx)) hbK
  have hJK : J.carrier ⊆ K.carrier := fun x hx => hLK (hJL hx)
  obtain ⟨σ,hρ,hτ,hr⟩ := PersistentRestrictionCode.restriction ρ τ hIK he hz
    hIJ hJK hj hpres hLK
  let s : S := ⟨σ,hr⟩
  have hwK : w s ∈ K.carrier := K.lower (hb (w s) (Or.inl ⟨s,rfl⟩)) hbK
  exact hw s hρ K hJK τ hwK hτ

end
end TuringRigidity.PersistentExtension

end OAI
