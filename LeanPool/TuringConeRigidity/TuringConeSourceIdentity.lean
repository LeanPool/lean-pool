/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeSourceIdentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeProgramGlobalization

/-!
# The source equation for inverse cone maps

The arithmetic SourceEquation is unchanged. The degree-theoretic hypothesis
is the relative minimal-pair identity over a join degree(Y), rather than over
degree(Y). The inverse-join map preserves joins even though it is not injective.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeSourceIdentity

open GenericIdentity ConeRigidity ConeProgramGlobalization

theorem imageJoin_degree {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : OracleCode) (P Y G : Oracle)
    (hG : RepresentsInverseAt e p P G)
    (hC : RepresentsInverseAt e p P (GenericCoding.code Y G))
    (hi : GenericCoding.InfiniteOdd G) :
    degree (ImageJoin p P Y G) = pullback e (degree (join Y G)) := by
  change degree (value p P (GenericCoding.code Y G)) ⊔ degree (value p P G) = _
  rw [hC.2, hG.2, ←pullback_sup]
  exact congrArg (pullback e) (GenericCoding.join_degree_eq Y G hi)

/-- Transport the relative principal-ideal intersection through e.symm. -/
theorem source_intersection {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : OracleCode) (P A Y G0 G1 : Oracle) (hA : degree A = a)
    (hG0 : RepresentsInverseAt e p P G0) (hG1 : RepresentsInverseAt e p P G1)
    (hC0 : RepresentsInverseAt e p P (GenericCoding.code Y G0))
    (hC1 : RepresentsInverseAt e p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection (join A Y) (join (join A Y) G0) (join (join A Y) G1)) :
    ∀ b : Degree, b ≤ pullback e (degree Y) ↔
      b ≤ degree (ImageJoin p P Y G0) ∧ b ≤ degree (ImageJoin p P Y G1) := by
  rw [imageJoin_degree e p P Y G0 hG0 hC0 hi0,
    imageJoin_degree e p P Y G1 hG1 hC1 hi1]
  intro b
  simp only [le_pullback_iff]
  have h := hI (e b).val
  change ((e b).val ≤ degree A ⊔ degree Y ↔
    (e b).val ≤ (degree A ⊔ degree Y) ⊔ degree G0 ∧
    (e b).val ≤ (degree A ⊔ degree Y) ⊔ degree G1) at h
  change (e b).val ≤ a ⊔ degree Y ↔
    (e b).val ≤ a ⊔ (degree Y ⊔ degree G0) ∧
    (e b).val ≤ a ⊔ (degree Y ⊔ degree G1)
  simpa only [hA, sup_assoc] using h

/-- The same arithmetic equation characterizes inverse representation once
its four auxiliary values are correct and the generics form a relative pair. -/
theorem source_equation_iff {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : OracleCode) (P A Y G0 G1 : Oracle) (hA : degree A = a)
    (hG0 : RepresentsInverseAt e p P G0) (hG1 : RepresentsInverseAt e p P G1)
    (hC0 : RepresentsInverseAt e p P (GenericCoding.code Y G0))
    (hC1 : RepresentsInverseAt e p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection (join A Y) (join (join A Y) G0) (join (join A Y) G1)) :
    SourceEquation p P (Y, G0, G1) ↔ RepresentsInverseAt e p P Y := by
  have h := source_intersection e p P A Y G0 G1 hA hG0 hG1 hC0 hC1 hi0 hi1 hI
  constructor
  · rintro ⟨hY, _, _, _, _, he⟩
    refine ⟨hY, le_antisymm ?_ ?_⟩
    · exact (h _).mpr ((he _).mp le_rfl)
    · exact (he _).mpr ((h _).mp le_rfl)
  · rintro ⟨hY, hdeg⟩
    refine ⟨hY, hG0.1, hG1.1, hC0.1, hC1.1, ?_⟩
    intro b
    change b ≤ degree (value p P Y) ↔ _
    rw [hdeg]
    exact h b

end OAI.TuringRigidity.ConeSourceIdentity
