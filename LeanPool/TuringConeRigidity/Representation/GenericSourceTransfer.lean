/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GenericSourceTransfer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.GenericTruth
public import LeanPool.TuringConeRigidity.Representation.GenericFiberIdeal
public import LeanPool.TuringConeRigidity.Representation.SourceIdentity

/-!
# Generic Source Transfer
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GenericSourceTransfer
open FiniteShuffle ShuffleRequirements PairGenericSelection GenericFactor GenericIdentity Set

@[simp] theorem triple_join (Y Z : Oracle) :
    GenericTruth.triple (join Y Z) = (Y,column false Z,column true Z) := by
  have hl : column false (join Y Z) = Y := by funext n; simp [column]
  have hr : column true (join Y Z) = Z := by funext n; simp [column]
  simp [GenericTruth.triple,hl,hr]

theorem selected_borel_truth (p : OracleCode) (P : Oracle)
    (E : ℕ → List Bool → Prop) (hE : ∀ n, DenseOpen (E n)) :
    ∃ U : Set Oracle, IsOpen U ∧
    ∃ F : ℕ → List Bool → Prop, (∀ n, DenseOpen (F n)) ∧
    ∃ Z : {Y : Oracle // GenericFor F Y} → Oracle, Measurable Z ∧
      (∀ Y b, GenericFor E (column b (Z Y)) ∧ GenericCoding.InfiniteOdd (column b (Z Y)) ∧
        ∀ X, GenericFor E (GenericCoding.code X (column b (Z Y)))) ∧
      (∀ Y a, a ≤ degree Y.val ↔
        a ≤ degree (join Y.val (column false (Z Y))) ∧
        a ≤ degree (join Y.val (column true (Z Y)))) ∧
      ∀ Y, SourceEquation p P (Y.val,column false (Z Y),column true (Z Y)) ↔
        join Y.val (Z Y) ∈ U := by
  obtain ⟨U,hU,D,hD,htruth⟩ := GenericTruth.sourceEquation_generic_truth p P
  obtain ⟨hF,Z,hZ,hjoint,hgen,hI⟩ := borel_joint_ideal_selection D E hD hE
  refine ⟨U,hU,FirstFamily D,hF,Z,hZ,hgen,hI,?_⟩
  intro Y
  simpa only [triple_join] using htruth (join Y.val (Z Y)) (hjoint Y)

theorem recover_at (π : Degree ≃o Degree) (p : OracleCode) (P Y G0 G1 : Oracle)
    (hG0 : RepresentsAt π p P G0) (hG1 : RepresentsAt π p P G1)
    (hC0 : RepresentsAt π p P (GenericCoding.code Y G0))
    (hC1 : RepresentsAt π p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection Y (join Y G0) (join Y G1))
    (he : SourceEquation p P (Y, G0, G1)) : RepresentsAt π p P Y :=
  (source_5_5_iff π p P Y G0 G1 hG0 hG1 hC0 hC1 hi0 hi1 hI).mp he

end TuringRigidity.GenericSourceTransfer

end OAI
