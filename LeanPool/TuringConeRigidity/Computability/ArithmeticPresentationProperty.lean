/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticPresentationProperty.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticPersistence

/-!
# Arithmetic Presentation Property
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open EncodedForcing OracleJump UniformArithmetic PersistentRestrictions
open PersistentPresentation NumericalAutomorphism
noncomputable section

/-- The columns enumerate a degree ideal closed downward and under binary joins. -/
def IdealCode (A : Oracle) : Prop :=
  (∀ n e, IndexPresentation.Dom (columns A n) e →
    ∃ m, IndexPresentation.value (columns A n) e = degree (columns A m)) ∧
  ∀ n m, ∃ k, degree (columns A n) ⊔ degree (columns A m) = degree (columns A k)

/-- The countable degree ideal represented by the columns of the code. -/
def idealOfCode (A : Oracle) (h : IdealCode A) : CountableIdeal where
  carrier := Set.range (fun n => degree (columns A n))
  nonempty := ⟨degree (columns A 0),0,rfl⟩
  countable := Set.countable_range _
  lower := by
    intro a b hab hb
    obtain ⟨n,rfl⟩ := hb
    obtain ⟨e,he,hv⟩ := IndexPresentation.value_surjective (columns A n) a hab
    obtain ⟨m,hm⟩ := h.1 n e he
    exact ⟨m,hm.symm.trans hv⟩
  join_mem := by
    intro a b ha hb
    obtain ⟨n,rfl⟩ := ha
    obtain ⟨m,rfl⟩ := hb
    obtain ⟨k,hk⟩ := h.2 n m
    exact ⟨k,hk.symm⟩

theorem ideal_code {I : CountableIdeal} {A : Oracle} (hA : Presented I A) : IdealCode A := by
  constructor
  · intro n e _
    obtain ⟨m,hm⟩ := (hA _).mp
      (I.lower (IndexPresentation.value_below (columns A n) e) (entry hA n).property)
    exact ⟨m,hm.symm⟩
  · intro n m
    obtain ⟨k,hk⟩ := (hA _).mp (I.join_mem (entry hA n).property (entry hA m).property)
    exact ⟨k,hk.symm⟩

/-- A coded ideal containing the zero jump, together with an action coded by `R`. -/
def Base (A R : Oracle) : Prop :=
  IdealCode A ∧ (∃ n, degree (jump FixedArithmetic.zero) = degree (columns A n)) ∧
    Action A (fun v => R v = true)

/-- A persistent automorphism of a presented countable ideal containing the zero jump, with
graph coded by `R`. -/
def Property (A R : Oracle) : Prop :=
  ∃ I : CountableIdeal, ∃ hA : Presented I A,
    degree (jump FixedArithmetic.zero) ∈ I.carrier ∧
      ∃ ρ : I ≃o I, (∀ v, R v = true ↔ Graph ρ hA v) ∧ Persistent I ρ

theorem property_iff (A R : Oracle) : Property A R ↔ Base A R ∧ Criterion A R := by
  constructor
  · rintro ⟨I,hA,hz,ρ,hR,hp⟩
    have ha : Action A (fun v => R v = true) :=
      (PersistenceCriterion.action_congr hR).mpr (action_of_automorphism hA ρ)
    obtain ⟨n,hn⟩ := (hA _).mp hz
    exact ⟨⟨ideal_code hA,⟨n,hn.symm⟩,ha⟩,(persistent_iff hA ρ hz hR).mp hp⟩
  · rintro ⟨⟨hi,⟨n,hn⟩,ha⟩,hc⟩
    let I := idealOfCode A hi
    have hA : Presented I A := fun _ => Iff.rfl
    have hz : degree (jump FixedArithmetic.zero) ∈ I.carrier := (hA _).mpr ⟨n,hn.symm⟩
    obtain ⟨ρ,hR⟩ := reconstruct hA ha
    exact ⟨I,hA,hz,ρ,hR,(persistent_iff hA ρ hz hR).mpr hc⟩

theorem base_arith : Arith (fun O (_ : ℕ) => Base (O 0) (O 1)) := by
  have hA := parameter_arith 0
  have hR := parameter_arith 1
  have hz : ArithmeticOracle (fun _ _ => FixedArithmetic.zero) := by
    exact (equal (Primrec.const 0) (Primrec.const 1)).congr
      (fun _ _ => by simp [FixedArithmetic.zero])
  have hz' := (degree_equal_arith (jump_arith hz) (column_arith hA
    UniformArithmetic.right_primrec)).ex
  have hi := (lower_arith hA).and (join_closed_arith hA)
  exact (hi.and (hz'.and (action_arith hA hR))).congr
    (fun _ _ => by simp only [Base,IdealCode,UniformArithmetic.right,Nat.unpair_pair])

/-- The three-oracle environment containing the ideal, action, and test-extension codes. -/
def parameters (A R H : Oracle) : Oracles
  | 0 => A
  | 1 => R
  | _ => H

/-- A two-oracle predicate has an arithmetic matrix universally quantified over one further
oracle. -/
def PiOneOne (P : Oracle → Oracle → Prop) : Prop :=
  ∃ Q : Predicate, Arith Q ∧ ∀ A R, P A R ↔ ∀ H : Oracle, Q (parameters A R H) 0

theorem source_4_2_1 : PiOneOne Property := by
  refine ⟨fun O v => Base (O 0) (O 1) ∧ Matrix O v,
    base_arith.and matrix_arith,fun A R => ?_⟩
  rw [property_iff]
  change Base A R ∧ Criterion A R ↔ ∀ H, Base A R ∧
    (NumericalIdeal.JumpCode H → NumericalIdeal.Includes A H →
      ∃ e, NumericalAutomorphism.Action H (fun v => tableOracle (iterate H 11) e v = true) ∧
        NumericalExtension.Compatible A H (fun v => R v = true)
          (fun v => tableOracle (iterate H 11) e v = true))
  exact ⟨fun h H => ⟨h.1,h.2 H⟩,fun h => ⟨(h FixedArithmetic.zero).1,fun H => (h H).2⟩⟩

end
end TuringRigidity.ArithmeticPersistence

end OAI
