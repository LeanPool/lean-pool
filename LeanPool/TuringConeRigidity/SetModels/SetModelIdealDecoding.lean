/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelIdealDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelPersistentSatisfaction

/-!
# Set Model Ideal Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem externally_countable (C : Context M) {a : ZFSet.{u}} (ha : a ∈ M)
    (hct : InternallyCountable M a) : (a : Set ZFSet.{u}).Countable := by
  obtain ⟨f,hf,hfg,hfo⟩ := countable_graph C ha hct
  have hex (n : ℕ) : ∃ y, y ∈ a ∧ ZFSet.pair (natSet n) y ∈ f := by
    obtain ⟨y,hy,hny,_⟩ := hfg.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
    exact ⟨y,hy,hny⟩
  choose F hF using hex
  apply (Set.countable_range F).mono
  intro x hx
  obtain ⟨n,hn⟩ := hfo x hx
  exact ⟨n,hfg.unique ((mem_omega _).mpr ⟨n,rfl⟩) (hF n).1 hx (hF n).2 hn⟩

theorem decode_ideal (C : Context M) {D L a : ZFSet.{u}}
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (haM : a ∈ M) (ha : IsIdeal a D L) (hct : InternallyCountable M a) :
    ∃ I : CountableIdeal, idealSet I = a := by
  let K : Set Degree := {b | degreeSet b ∈ a}
  have hrep {b : Degree} (hb : b ∈ K) : ∃ B ∈ reals M, degree B = b := by
    obtain ⟨B,hB,hb'⟩ := (hD _).mp (ha.1 (show degreeSet b ∈ a from hb))
    exact ⟨B,hB,(degreeSet_injective hb').symm⟩
  have hlo {b c : Degree} (hbc : b ≤ c) (hc : c ∈ K) : b ∈ K := by
    obtain ⟨B,rfl⟩ := degree_surjective b
    obtain ⟨C',hC',hCc⟩ := hrep hc
    have hBC : Reduces B C' := by change degree B ≤ degree C'; rw [hCc]; exact hbc
    have hB := lower_mem C hC' hBC
    have hDB : degreeSet (degree B) ∈ D := (hD _).mpr ⟨B,hB,rfl⟩
    apply ha.2.2.1 (degreeSet c) hc _ hDB
    rw [←hCc]
    exact (hL B hB C' hC').mpr hBC
  have hne : K.Nonempty := by
    obtain ⟨x,hx⟩ := ha.2.1
    obtain ⟨A,hA,hxA⟩ := (hD x).mp (ha.1 hx)
    exact ⟨degree A,by change degreeSet (degree A) ∈ a; rw [←hxA]; exact hx⟩
  have hcount : K.Countable :=
    (externally_countable C haM hct).preimage degreeSet_injective
  have hjoin {b c : Degree} (hb : b ∈ K) (hc : c ∈ K) : b⊔c ∈ K := by
    obtain ⟨z,hz,hbz,hcz⟩ := ha.2.2.2 (degreeSet b) hb (degreeSet c) hc
    obtain ⟨A,hA,hzA⟩ := (hD z).mp (ha.1 hz)
    have hzK : degree A ∈ K := by change degreeSet (degree A) ∈ a; rw [←hzA]; exact hz
    have hbM := C.transitive _ haM (degreeSet b) hb
    have hcM := C.transitive _ haM (degreeSet c) hc
    have hzM := C.transitive _ haM _ hz
    rw [hzA] at hbz hcz hzM
    have hbA := (order_code C hL hbM hzM).mp hbz
    have hcA := (order_code C hL hcM hzM).mp hcz
    exact hlo (sup_le hbA hcA) hzK
  let I : CountableIdeal := ⟨K,hne,hcount,fun {_ _} h h' => hlo h h',fun {_ _} h h' => hjoin h h'⟩
  refine ⟨I,?_⟩
  apply ZFSet.ext
  intro x
  rw [mem_idealSet]
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact hb
  · intro hx
    obtain ⟨A,hA,hxA⟩ := (hD x).mp (ha.1 hx)
    exact ⟨degree A,by change degreeSet (degree A) ∈ a; rw [←hxA]; exact hx,hxA⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
