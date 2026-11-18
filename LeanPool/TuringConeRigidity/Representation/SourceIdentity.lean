/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceIdentity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericIdentity
public import LeanPool.TuringConeRigidity.Representation.GenericRepresentation

/-!
# Source Identity
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericIdentity

/-- The program is total at `A` and its output degree equals the automorphism's value at
`degree A`. -/
def RepresentsAt (π : Degree ≃o Degree) (p : OracleCode) (P A : Oracle) : Prop :=
  Total p P A ∧ degree (value p P A) = π (degree A)

/-- Join the program's output on the generic code of `Y` with its output on `G`. -/
noncomputable def ImageJoin (p : OracleCode) (P Y G : Oracle) : Oracle :=
  join (value p P (GenericCoding.code Y G)) (value p P G)

theorem imageJoin_degree (π : Degree ≃o Degree) (p : OracleCode) (P Y G : Oracle)
    (hG : RepresentsAt π p P G) (hC : RepresentsAt π p P (GenericCoding.code Y G))
    (hi : GenericCoding.InfiniteOdd G) :
    degree (ImageJoin p P Y G) = π (degree (join Y G)) := by
  change degree (value p P (GenericCoding.code Y G)) ⊔ degree (value p P G) = _
  rw [hC.2,hG.2,←π.map_sup]
  exact congrArg π (GenericCoding.join_degree_eq Y G hi)

theorem source_5_4 (π : Degree ≃o Degree) (p : OracleCode) (P Y G0 G1 : Oracle)
    (hG0 : RepresentsAt π p P G0) (hG1 : RepresentsAt π p P G1)
    (hC0 : RepresentsAt π p P (GenericCoding.code Y G0))
    (hC1 : RepresentsAt π p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection Y (join Y G0) (join Y G1)) :
    ∀ b : Degree, b ≤ π (degree Y) ↔
      b ≤ degree (ImageJoin p P Y G0) ∧ b ≤ degree (ImageJoin p P Y G1) := by
  rw [imageJoin_degree π p P Y G0 hG0 hC0 hi0,
    imageJoin_degree π p P Y G1 hG1 hC1 hi1]
  exact common_lower_transport π _ _ _ hI

theorem source_5_5_iff (π : Degree ≃o Degree) (p : OracleCode) (P Y G0 G1 : Oracle)
    (hG0 : RepresentsAt π p P G0) (hG1 : RepresentsAt π p P G1)
    (hC0 : RepresentsAt π p P (GenericCoding.code Y G0))
    (hC1 : RepresentsAt π p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection Y (join Y G0) (join Y G1)) :
    SourceEquation p P (Y,G0,G1) ↔ RepresentsAt π p P Y := by
  have h := source_5_4 π p P Y G0 G1 hG0 hG1 hC0 hC1 hi0 hi1 hI
  constructor
  · rintro ⟨hY,_,_,_,_,he⟩
    refine ⟨hY,le_antisymm ?_ ?_⟩
    · exact (h _).mpr ((he _).mp le_rfl)
    · exact (he _).mpr ((h _).mp le_rfl)
  · rintro ⟨hY,hdeg⟩
    refine ⟨hY,hG0.1,hG1.1,hC0.1,hC1.1,?_⟩
    intro b
    change b ≤ degree (value p P Y) ↔ _
    rw [hdeg]
    exact h b

theorem selected_source_equation (D : ℕ → List Bool → Prop)
    (hD : ∀ n, FiniteShuffle.DenseOpen (D n)) :
    ∃ G : Bool → Oracle → Oracle, (∀ b, Measurable (G b)) ∧
      (∀ Y b, ShuffleRequirements.GenericFor D (G b Y) ∧
        ∀ X, ShuffleRequirements.GenericFor D (GenericCoding.code X (G b Y))) ∧
      ∀ (π : Degree ≃o Degree) p P Y,
        (∀ b, RepresentsAt π p P (G b Y)) →
        (∀ b, RepresentsAt π p P (GenericCoding.code Y (G b Y))) →
        (SourceEquation p P (Y,G false Y,G true Y) ↔ RepresentsAt π p P Y) := by
  obtain ⟨G,hG,hgen,hI⟩ := selected_generic_ideal D hD
  refine ⟨G,hG,fun Y b => ⟨(hgen Y b).1,(hgen Y b).2.2⟩,?_⟩
  intro π p P Y hg hc
  exact source_5_5_iff π p P Y (G false Y) (G true Y) (hg false) (hg true)
    (hc false) (hc true) (hgen Y false).2.1 (hgen Y true).2.1 (hI Y)

end TuringRigidity.GenericIdentity

end OAI
