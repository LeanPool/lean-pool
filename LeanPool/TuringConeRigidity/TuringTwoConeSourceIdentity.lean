/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeSourceIdentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeProgramGlobalization
public import LeanPool.TuringConeRigidity.Representation.SourceIdentity

/-!
# The arithmetic source equation for joined inverses between two cones

The relative minimal pair is taken over the target base joined with Y.
Ordinary common lower bounds need not lie above the source base; the checked
le_pullback_iff adjoins that base before applying the order isomorphism.
The arithmetic SourceEquation itself and its complexity are unchanged.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeSourceIdentity

open GenericIdentity TwoConeRigidity TwoConeProgramGlobalization

theorem imageJoin_degree {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (p : OracleCode) (P Y G : Oracle)
    (hG : RepresentsInverseAt e p P G)
    (hC : RepresentsInverseAt e p P (GenericCoding.code Y G))
    (hi : GenericCoding.InfiniteOdd G) :
    degree (ImageJoin p P Y G) = pullback e (degree (join Y G)) := by
  change degree (value p P (GenericCoding.code Y G)) ⊔ degree (value p P G) = _
  rw [hC.2, hG.2, ← pullback_sup]
  exact congrArg (pullback e) (GenericCoding.join_degree_eq Y G hi)

theorem source_intersection {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (p : OracleCode) (P B Y G0 G1 : Oracle) (hB : degree B = b)
    (hG0 : RepresentsInverseAt e p P G0) (hG1 : RepresentsInverseAt e p P G1)
    (hC0 : RepresentsInverseAt e p P (GenericCoding.code Y G0))
    (hC1 : RepresentsInverseAt e p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection (join B Y) (join (join B Y) G0) (join (join B Y) G1)) :
    ∀ z : Degree, z ≤ pullback e (degree Y) ↔
      z ≤ degree (ImageJoin p P Y G0) ∧ z ≤ degree (ImageJoin p P Y G1) := by
  rw [imageJoin_degree e p P Y G0 hG0 hC0 hi0,
    imageJoin_degree e p P Y G1 hG1 hC1 hi1]
  intro z
  simp only [le_pullback_iff]
  have h := hI (imageJoin e z)
  change (imageJoin e z ≤ degree B ⊔ degree Y ↔
    imageJoin e z ≤ (degree B ⊔ degree Y) ⊔ degree G0 ∧
    imageJoin e z ≤ (degree B ⊔ degree Y) ⊔ degree G1) at h
  change imageJoin e z ≤ b ⊔ degree Y ↔
    imageJoin e z ≤ b ⊔ (degree Y ⊔ degree G0) ∧
    imageJoin e z ≤ b ⊔ (degree Y ⊔ degree G1)
  simpa only [hB, sup_assoc] using h

theorem source_equation_iff {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (p : OracleCode) (P B Y G0 G1 : Oracle) (hB : degree B = b)
    (hG0 : RepresentsInverseAt e p P G0) (hG1 : RepresentsInverseAt e p P G1)
    (hC0 : RepresentsInverseAt e p P (GenericCoding.code Y G0))
    (hC1 : RepresentsInverseAt e p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection (join B Y) (join (join B Y) G0) (join (join B Y) G1)) :
    SourceEquation p P (Y, G0, G1) ↔ RepresentsInverseAt e p P Y := by
  have h := source_intersection e p P B Y G0 G1 hB hG0 hG1 hC0 hC1 hi0 hi1 hI
  constructor
  · rintro ⟨hY, _, _, _, _, he⟩
    refine ⟨hY, le_antisymm ?_ ?_⟩
    · exact (h _).mpr ((he _).mp le_rfl)
    · exact (he _).mpr ((h _).mp le_rfl)
  · rintro ⟨hY, hdeg⟩
    refine ⟨hY, hG0.1, hG1.1, hC0.1, hC1.1, ?_⟩
    intro z
    change z ≤ degree (value p P Y) ↔ _
    rw [hdeg]
    exact h z

end OAI.TuringRigidity.TwoConeSourceIdentity
