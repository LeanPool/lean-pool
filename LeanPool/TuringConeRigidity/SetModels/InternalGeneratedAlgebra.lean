/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalGeneratedAlgebra.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanSyntax

/-!
# Internal Generated Algebra
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalGeneratedAlgebra
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanSyntax

/-- The intersection of all candidate Boolean subalgebras containing the seeds. -/
noncomputable def generated (c B Q S : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∀ A ∈ candidates c B Q S, U ∈ A)

theorem generated_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) :
    generated c B Q S ∈ M := by
  have hk := candidates_mem M c B Q S hM hT hc hB hQ hS
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.allMem 1 (.member 1 0)) (fun _ => candidates c B Q S) (fun _ => hk) hB
  simpa only [generated,Formula.eval_allMem,Formula.Eval,cons_zero,cons_succ] using hs

theorem generated_subset (c B Q S : ZFSet.{0}) : generated c B Q S ⊆ B :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem seeds_subset (c B Q S : ZFSet.{0}) (hS : S ⊆ B) : S ⊆ generated c B Q S := by
  intro U hU
  refine ZFSet.mem_sep.mpr ⟨hS hU,fun A hA => ?_⟩
  exact (ZFSet.mem_sep.mp hA).2.1 hU

theorem generated_le (c B Q S A : ZFSet.{0}) (hA : A ∈ Q)
    (hS : S ⊆ A) (hc : Closed c B Q A) : generated c B Q S ⊆ A := by
  intro U hU
  exact (ZFSet.mem_sep.mp hU).2 A (ZFSet.mem_sep.mpr ⟨hA,hS,hc⟩)

theorem algebra_closed (M c B Q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) : Closed c B Q B := by
  refine ⟨fun _ h => h,fun U hU => internal_complement M c B hM hT hc hB hU,?_⟩
  intro F hF _
  exact internal_join M c B F hM hT hc hB ((hQ F).mp hF).1

theorem generated_closed (c B Q S : ZFSet.{0}) (hB : Closed c B Q B) :
    Closed c B Q (generated c B Q S) := by
  refine ⟨generated_subset c B Q S,?_,?_⟩
  · intro U hU
    obtain ⟨hUB,hU⟩ := ZFSet.mem_sep.mp hU
    refine ZFSet.mem_sep.mpr ⟨hB.2.1 U hUB,fun A hA => ?_⟩
    exact (ZFSet.mem_sep.mp hA).2.2.2.1 U (hU A hA)
  · intro F hF hFS
    refine ZFSet.mem_sep.mpr ⟨hB.2.2 F hF (fun U hU => generated_subset c B Q S (hFS hU)),?_⟩
    intro A hA
    apply (ZFSet.mem_sep.mp hA).2.2.2.2 F hF
    intro U hU
    exact (ZFSet.mem_sep.mp (hFS hU)).2 A hA

theorem internal_generated_part (M c S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hS : S ∈ M) (hSc : ∀ U ∈ S, IsCode c U) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = generated c B Q S ∧ S ⊆ A ∧ A ∈ Q ∧ Closed c B Q A ∧
      ∀ A' ∈ Q, S ⊆ A' → Closed c B Q A' → A ⊆ A' := by
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hBM
  have hSB : S ⊆ B := fun U hU => (hB U).mpr ⟨hM S hS U hU,hSc U hU⟩
  have hA := generated_mem M c B Q S hM hT hc hBM hQM hS
  refine ⟨B,hBM,Q,hQM,generated c B Q S,hA,hB,hQ,rfl,seeds_subset c B Q S hSB,
    (hQ _).mpr ⟨hA,generated_subset c B Q S⟩,
    generated_closed c B Q S (algebra_closed M c B Q hM hT hc hB hQ),?_⟩
  exact fun A' hA' hSA' hclosed => generated_le c B Q S A' hA' hSA' hclosed

end TuringRigidity.InternalGeneratedAlgebra

end OAI
