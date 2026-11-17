/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeIdealCopies.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeIdealCodes

/-!
# Transport bounded unary copies between two ideal cones

All parameters must lie above the source base and below a point of its ideal.
The transported copy has the identical predicate on the standard naturals.
Ambient cone points outside the target ideal cannot satisfy its bounded codes;
this is proved explicitly rather than assumed in the copy specification.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeIdealCodes

open IdealInterpretation SetCoding RelationCoding BoundedDecoding ConeRelativeCoding
open ArithmeticModelDecoding

noncomputable section

variable {I : DegreeIdeal} {a : I}

/-- Regard a degree between the cone base and `z` as an element of the ideal's principal cone. -/
def boundedElement (z : Set.Ici a) (x : Degree) (ha : a.val ≤ x) (hz : x ≤ val z) :
    Set.Ici a := ⟨⟨x, I.lower hz z.val.property⟩, Set.mem_Ici.mpr ha⟩

/-- Lift an externally bounded antichain code into the ideal's principal cone. -/
def liftAntichain (z : Set.Ici a) (p : AntichainCode)
    (ha : AntichainAbove p a.val) (hz : AntichainBelow p (val z)) : ACode a :=
  ⟨boundedElement z p.bound ha.1 hz.1, boundedElement z p.left ha.2.1 hz.2.1,
    boundedElement z p.right ha.2.2 hz.2.2⟩

@[simp] theorem liftAntichain_external (z : Set.Ici a) (p : AntichainCode)
    (ha : AntichainAbove p a.val) (hz : AntichainBelow p (val z)) :
    (liftAntichain z p ha hz).external = p := by cases p; rfl

/-- Lift an externally bounded set code into the ideal's principal cone. -/
def liftSet (z : Set.Ici a) (p : SetCode)
    (ha : SetAbove p a.val) (hz : SetBelow p (val z)) : SCode a :=
  ⟨boundedElement z p.bound ha.1 hz.1,
    liftAntichain z p.tags ha.2.1 hz.2.1,
    liftAntichain z p.decorated ha.2.2 hz.2.2⟩

@[simp] theorem liftSet_external (z : Set.Ici a) (p : SetCode)
    (ha : SetAbove p a.val) (hz : SetBelow p (val z)) :
    (liftSet z p ha hz).external = p := by cases p; rfl

/-- Lift an externally bounded relation code into the ideal's principal cone. -/
def liftRelation (z : Set.Ici a) {n : ℕ} (p : RelationCode n)
    (ha : RelationAbove p a.val) (hz : RelationBelow p (val z)) : RCode a n :=
  ⟨fun i => liftSet z (p.coordinates i) (ha.1 i) (hz.1 i),
    liftAntichain z p.tuples ha.2 hz.2⟩

@[simp] theorem liftRelation_external (z : Set.Ici a) {n : ℕ} (p : RelationCode n)
    (ha : RelationAbove p a.val) (hz : RelationBelow p (val z)) :
    (liftRelation z p ha hz).external = p := by cases p; rfl

/-- Transport a bounded copy without changing the represented predicate. -/
theorem transport_copy {J : DegreeIdeal} {b : J} {U : ℕ → Prop}
    (ρ : Set.Ici a ≃o Set.Ici b) (c : ConeCoding.Copy a.val U) (z : Set.Ici a)
    (haS : RelationAbove c.successor a.val) (haP : RelationAbove c.predicate a.val)
    (hS : RelationBelow c.successor (val z)) (hP : RelationBelow c.predicate (val z)) :
    ∃ d : ConeCoding.Copy b.val U,
      RelationAbove d.successor b.val ∧ RelationAbove d.predicate b.val ∧
      RelationBelow d.successor (val (ρ z)) ∧ RelationBelow d.predicate (val (ρ z)) := by
  let S := liftRelation z c.successor haS hS
  let P := liftRelation z c.predicate haP hP
  have hn (n : ℕ) : (c.node n).val ∈ I.carrier := by
    obtain ⟨tags, ht, _⟩ := (c.successor_spec (c.node n) (c.node (n + 1))).mpr ⟨n, rfl, rfl⟩
    exact I.lower ((ht 0).2.1.trans (hS.1 0).1) z.val.property
  let node (n : ℕ) : Set.Ici a :=
    ⟨⟨(c.node n).val, hn n⟩, Set.mem_Ici.mpr (Set.mem_Ici.mp (c.node n).property)⟩
  let newNode (n : ℕ) : Set.Ici b.val := ambient (ρ (node n))
  have hnode (n : ℕ) : ambient (node n) = c.node n := rfl
  have heq (x : Set.Ici b) (k : ℕ) :
      ambient (ρ.symm x) = c.node k ↔ x = ρ (node k) := by
    constructor
    · intro h
      have h' : ρ.symm x = node k := ambient_injective (h.trans (hnode k).symm)
      exact (ρ.apply_symm_apply x).symm.trans (congrArg ρ h')
    · intro h
      rw [h, ρ.symm_apply_apply]
      exact hnode k
  have hi : Function.Injective newNode := by
    intro i j h
    have h' : node i = node j := ρ.injective (ambient_injective h)
    exact c.injective ((hnode i).symm.trans ((congrArg ambient h').trans (hnode j)))
  have hs (x y : Set.Ici b) :
      ConeCoding.Holds b.val (S.map ρ).external (two (val x) (val y)) ↔
        ∃ k, x = ρ (node k) ∧ y = ρ (node (k + 1)) := by
    have hh := S.transport_two ρ (ρ.symm x) (ρ.symm y)
    simp only [ρ.apply_symm_apply, S, liftRelation_external] at hh
    rw [hh]
    change ConeCoding.Holds a.val c.successor
      (two (ambient (ρ.symm x)).val (ambient (ρ.symm y)).val) ↔ _
    rw [c.successor_spec]
    exact exists_congr (fun k => and_congr (heq x k) (heq y (k + 1)))
  have hp (x : Set.Ici b) :
      ConeCoding.Holds b.val (P.map ρ).external (one (val x)) ↔
        ∃ k, U k ∧ x = ρ (node k) := by
    have hh := P.transport_one ρ (ρ.symm x)
    simp only [ρ.apply_symm_apply, P, liftRelation_external] at hh
    rw [hh]
    change ConeCoding.Holds a.val c.predicate (one (ambient (ρ.symm x)).val) ↔ _
    rw [c.predicate_spec]
    exact exists_congr (fun k => and_congr_right (fun _ => heq x k))
  have hs' (x y : Set.Ici b.val) :
      ConeCoding.Holds b.val (S.map ρ).external (two x.val y.val) ↔
        ∃ k, x = newNode k ∧ y = newNode (k + 1) := by
    constructor
    · intro h
      let x' : Set.Ici b := ⟨⟨x.val, (S.map ρ).coordinates_mem h 0⟩,
        Set.mem_Ici.mpr (Set.mem_Ici.mp x.property)⟩
      let y' : Set.Ici b := ⟨⟨y.val, (S.map ρ).coordinates_mem h 1⟩,
        Set.mem_Ici.mpr (Set.mem_Ici.mp y.property)⟩
      obtain ⟨k, hk, hl⟩ := (hs x' y').mp h
      exact ⟨k, Subtype.ext (congrArg val hk), Subtype.ext (congrArg val hl)⟩
    · rintro ⟨k, rfl, rfl⟩
      exact (hs (ρ (node k)) (ρ (node (k + 1)))).mpr ⟨k, rfl, rfl⟩
  have hp' (x : Set.Ici b.val) :
      ConeCoding.Holds b.val (P.map ρ).external (one x.val) ↔
        ∃ k, U k ∧ x = newNode k := by
    constructor
    · intro h
      let x' : Set.Ici b := ⟨⟨x.val, (P.map ρ).coordinates_mem h 0⟩,
        Set.mem_Ici.mpr (Set.mem_Ici.mp x.property)⟩
      obtain ⟨k, hk, he⟩ := (hp x').mp h
      exact ⟨k, hk, Subtype.ext (congrArg val he)⟩
    · rintro ⟨k, hk, rfl⟩
      exact (hp (ρ (node k))).mpr ⟨k, hk, rfl⟩
  let d : ConeCoding.Copy b.val U :=
    ⟨newNode, hi, (S.map ρ).external, (P.map ρ).external, hs', hp'⟩
  refine ⟨d, (S.map ρ).above, (P.map ρ).above, ?_, ?_⟩
  · exact S.map_below ρ z (by simpa only [S, liftRelation_external] using hS)
  · exact P.map_below ρ z (by simpa only [P, liftRelation_external] using hP)

end
end OAI.TuringRigidity.TwoConeIdealCodes
