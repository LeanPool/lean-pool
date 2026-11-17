/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IdealLift.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.IdealInterpretation
public import LeanPool.TuringConeRigidity.Effective.CodingBounds

/-!
# Ideal Lift
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IdealInterpretation
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding

def ACode.ofBelow {I : DegreeIdeal} (p : AntichainCode) (b : I) (hp : AntichainBelow p b.val) :
  ACode I :=
  ⟨⟨p.bound,I.lower hp.1 b.property⟩,⟨p.left,I.lower hp.2.1 b.property⟩,
    ⟨p.right,I.lower hp.2.2 b.property⟩⟩

@[simp] theorem ACode.external_ofBelow {I : DegreeIdeal} (p : AntichainCode) (b : I)
    (hp : AntichainBelow p b.val) : (ACode.ofBelow p b hp).external = p := by cases p; rfl

def SCode.ofBelow {I : DegreeIdeal} (p : SetCode) (b : I) (hp : SetBelow p b.val) : SCode I :=
  ⟨⟨p.bound,I.lower hp.1 b.property⟩,ACode.ofBelow p.tags b hp.2.1,ACode.ofBelow p.decorated b
    hp.2.2⟩

@[simp] theorem SCode.external_ofBelow {I : DegreeIdeal} (p : SetCode) (b : I)
    (hp : SetBelow p b.val) : (SCode.ofBelow p b hp).external = p := by cases p; rfl

def RCode.ofBelow {I : DegreeIdeal} {n : ℕ} (p : RelationCode n) (b : I)
    (hp : RelationBelow p b.val) : RCode I n :=
  ⟨fun i => SCode.ofBelow (p.coordinates i) b (hp.1 i),ACode.ofBelow p.tuples b hp.2⟩

@[simp] theorem RCode.external_ofBelow {I : DegreeIdeal} {n : ℕ} (p : RelationCode n) (b : I)
    (hp : RelationBelow p b.val) : (RCode.ofBelow p b hp).external = p := by cases p; rfl

theorem ACode.map_below {I J : DegreeIdeal} (ρ : I ≃o J) (p : ACode I) (b : I)
    (hp : AntichainBelow p.external b.val) : AntichainBelow (p.map ρ).external (ρ b).val :=
  ⟨show ρ p.bound ≤ ρ b from ρ.monotone hp.1,
    show ρ p.left ≤ ρ b from ρ.monotone hp.2.1,
    show ρ p.right ≤ ρ b from ρ.monotone hp.2.2⟩

theorem SCode.map_below {I J : DegreeIdeal} (ρ : I ≃o J) (p : SCode I) (b : I)
    (hp : SetBelow p.external b.val) : SetBelow (p.map ρ).external (ρ b).val :=
  ⟨show ρ p.bound ≤ ρ b from ρ.monotone hp.1,p.tags.map_below ρ b hp.2.1,
    p.decorated.map_below ρ b hp.2.2⟩

theorem RCode.map_below {I J : DegreeIdeal} {n : ℕ} (ρ : I ≃o J) (p : RCode I n) (b : I)
    (hp : RelationBelow p.external b.val) : RelationBelow (p.map ρ).external (ρ b).val :=
  ⟨fun i => (p.coordinates i).map_below ρ b (hp.1 i),p.tuples.map_below ρ b hp.2⟩

theorem RCode.coordinates_mem {I : DegreeIdeal} {n : ℕ} (p : RCode I n) {v : Fin n → Degree}
    (h : p.external.Holds v) (i : Fin n) : v i ∈ I.carrier := by
  obtain ⟨c,hc,_⟩ := h
  exact I.lower (hc i).1 (p.coordinates i).bound.property

theorem RCode.transport_one {I J : DegreeIdeal} (ρ : I ≃o J) (p : RCode I 1) (a : I) :
    (p.map ρ).external.Holds (one (ρ a).val) ↔ p.external.Holds (one a.val) := by
  have hv : (fun _ : Fin 1 => (ρ a).val) = one (ρ a).val := by
    funext i; fin_cases i; rfl
  have hw : (fun _ : Fin 1 => a.val) = one a.val := by
    funext i; fin_cases i; rfl
  simpa only [hv,hw] using p.transport ρ (fun _ => a)

theorem RCode.transport_two {I J : DegreeIdeal} (ρ : I ≃o J) (p : RCode I 2) (a b : I) :
    (p.map ρ).external.Holds (two (ρ a).val (ρ b).val) ↔ p.external.Holds (two a.val b.val) := by
  have hv : (fun i : Fin 2 => (ρ (![a,b] i)).val) = two (ρ a).val (ρ b).val := by
    funext i; fin_cases i <;> rfl
  have hw : (fun i : Fin 2 => (![a,b] i).val) = two a.val b.val := by
    funext i; fin_cases i <;> rfl
  simpa only [hv,hw] using p.transport ρ ![a,b]

end TuringRigidity.IdealInterpretation

end OAI
