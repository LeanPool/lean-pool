/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericalIdeal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentPresentation

/-!
# Numerical Ideal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.NumericalIdeal
open EncodedForcing OracleJump IndexPresentation IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation
noncomputable section

/-- The oracle columns enumerate a lower, join-closed family also closed under the Turing
jump. -/
structure JumpCode (H : Oracle) : Prop where
  lower : ∀ n e, Dom (columns H n) e →
    ∃ m, value (columns H n) e = degree (columns H m)
  join : ∀ n m, ∃ k, degree (columns H n) ⊔ degree (columns H m) = degree (columns H k)
  jump : ∀ n, ∃ m, degreeJump (degree (columns H n)) = degree (columns H m)

/-- Decode a jump-closed column presentation as a countable degree ideal. -/
def decode (H : Oracle) (hc : JumpCode H) : CountableIdeal where
  carrier := Set.range (fun n => degree (columns H n))
  nonempty := ⟨degree (columns H 0),0,rfl⟩
  countable := Set.countable_range _
  lower := by
    intro a b hab hb
    obtain ⟨n,rfl⟩ := hb
    obtain ⟨e,he,hv⟩ := value_surjective (columns H n) a hab
    obtain ⟨m,hm⟩ := hc.lower n e he
    exact ⟨m,hm.symm.trans hv⟩
  join_mem := by
    intro a b ha hb
    obtain ⟨n,rfl⟩ := ha
    obtain ⟨m,rfl⟩ := hb
    obtain ⟨k,hk⟩ := hc.join n m
    exact ⟨k,hk.symm⟩

theorem decoded_presentation (H : Oracle) (hc : JumpCode H) : Presented (decode H hc) H :=
  fun _ => Iff.rfl

theorem decoded_closed (H : Oracle) (hc : JumpCode H) : JumpClosed (ideal (decode H hc)) := by
  intro x hx
  obtain ⟨n,rfl⟩ := hx
  obtain ⟨m,hm⟩ := hc.jump n
  exact ⟨m,hm.symm⟩

theorem code_of_ideal {J : CountableIdeal} {H : Oracle} (hp : Presented J H)
    (hj : JumpClosed (ideal J)) : JumpCode H := by
  constructor
  · intro n e _
    obtain ⟨m,hm⟩ := (hp _).mp (J.lower (value_below (columns H n) e) (entry hp n).property)
    exact ⟨m,hm.symm⟩
  · intro n m
    obtain ⟨k,hk⟩ := (hp _).mp (J.join_mem (entry hp n).property (entry hp m).property)
    exact ⟨k,hk.symm⟩
  · intro n
    obtain ⟨m,hm⟩ := (hp _).mp (hj _ (entry hp n).property)
    exact ⟨m,hm.symm⟩

/-- Every column degree represented by `A` is represented by some column of `H`. -/
def Includes (A H : Oracle) : Prop := ∀ n, ∃ m, degree (columns A n) = degree (columns H m)

theorem includes_iff {I J : CountableIdeal} {A H : Oracle}
    (hA : Presented I A) (hH : Presented J H) : Includes A H ↔ I.carrier ⊆ J.carrier := by
  constructor
  · intro h x hx
    obtain ⟨n,rfl⟩ := (hA x).mp hx
    obtain ⟨m,hm⟩ := h n
    exact (hH _).mpr ⟨m,hm.symm⟩
  · intro h n
    obtain ⟨m,hm⟩ := (hH _).mp (h (entry hA n).property)
    exact ⟨m,hm.symm⟩

end
end TuringRigidity.NumericalIdeal

end OAI
