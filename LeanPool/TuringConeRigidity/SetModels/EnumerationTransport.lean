/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/EnumerationTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GlobalLocality
public import LeanPool.TuringConeRigidity.SetModels.EnumerationDecoding

/-!
# Enumeration Transport
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EnumerationTransport
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding EnumerationDecoding
open IdealInterpretation GlobalLocality
noncomputable section

/-- Regard an arbitrary degree as an element of the full degree ideal. -/
def elem (a : Degree) : fullIdeal := ⟨a,Set.mem_univ _⟩
/-- Lift an external antichain code to a code internal to the full ideal. -/
def liftAntichain (p : AntichainCode) : ACode fullIdeal := ⟨elem p.bound,elem p.left,elem p.right⟩
/-- Lift an external degree-set code to a code internal to the full ideal. -/
def liftSet (p : SetCode) : SCode fullIdeal := ⟨elem p.bound,liftAntichain p.tags,liftAntichain
  p.decorated⟩
/-- Lift an external relation code to a code internal to the full ideal. -/
def liftRelation {n : ℕ} (p : RelationCode n) : RCode fullIdeal n :=
  ⟨fun i => liftSet (p.coordinates i),liftAntichain p.tuples⟩

@[simp] theorem lift_external {n : ℕ} (p : RelationCode n) : (liftRelation p).external = p := by
  cases p; rfl

/-- Transport a degree relation code through a global degree automorphism. -/
def mapRelation {n : ℕ} (π : Degree ≃o Degree) (p : RelationCode n) : RelationCode n :=
  ((liftRelation p).map (GlobalLocality.lift π)).external

theorem map_below {n : ℕ} (π : Degree ≃o Degree) (p : RelationCode n) (b : Degree)
    (hp : RelationBelow p b) : RelationBelow (mapRelation π p) (π b) := by
  exact (liftRelation p).map_below (GlobalLocality.lift π) (elem b) (by simpa only [lift_external,
    elem] using hp)

theorem map_two (π : Degree ≃o Degree) (p : RelationCode 2) (a b : Degree) :
    (mapRelation π p).Holds (two (π a) (π b)) ↔ p.Holds (two a b) := by
  have hv (x : Degree) : ((GlobalLocality.lift π) (elem x)).val = π x := rfl
  have he (x : Degree) : (elem x).val = x := rfl
  simpa only [lift_external,hv,he,mapRelation] using (liftRelation p).transport_two
    (GlobalLocality.lift π) (elem a) (elem b)

theorem inverse_eq (π : Degree ≃o Degree) (a b : Degree) : π.symm a = b ↔ a = π b := by
  constructor
  · intro h
    have hh := congrArg π h
    simpa only [π.apply_symm_apply] using hh
  · intro h
    rw [h,π.symm_apply_apply]

/-- Transport an entire degree-coded enumeration through a global degree automorphism. -/
def mapEnumeration (π : Degree ≃o Degree) (c : Enumeration) : Enumeration where
  node := fun n => π (c.node n)
  injective := π.injective.comp c.injective
  output := fun n => π (c.output n)
  successor := mapRelation π c.successor
  payload := mapRelation π c.payload
  successor_spec := by
    intro a b
    have hh := map_two π c.successor (π.symm a) (π.symm b)
    simp only [π.apply_symm_apply] at hh
    rw [hh,c.successor_spec]
    exact exists_congr (fun k => and_congr (inverse_eq π a (c.node k)) (inverse_eq π b (c.node
      (k+1))))
  payload_spec := by
    intro a b
    have hh := map_two π c.payload (π.symm a) (π.symm b)
    simp only [π.apply_symm_apply] at hh
    rw [hh,c.payload_spec]
    exact exists_congr (fun k => and_congr (inverse_eq π a (c.node k)) (inverse_eq π b (c.output
      k)))

theorem mapEnumeration_below (π : Degree ≃o Degree) (c : Enumeration) (b : Degree)
    (hS : RelationBelow c.successor b) (hP : RelationBelow c.payload b) :
    RelationBelow (mapEnumeration π c).successor (π b) ∧ RelationBelow (mapEnumeration π
      c).payload (π b) :=
  ⟨map_below π _ b hS,map_below π _ b hP⟩

end
end TuringRigidity.EnumerationTransport

end OAI
