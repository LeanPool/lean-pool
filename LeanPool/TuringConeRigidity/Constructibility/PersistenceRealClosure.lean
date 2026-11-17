/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/PersistenceRealClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.JumpIdealPresentation

/-!
# Persistence Real Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.PersistenceRealClosure
open EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic JumpIdealPresentation
open PersistentRestrictions PersistentPresentation PersistentCountability NumericalIdeal
open NumericalAutomorphism NumericalExtension
noncomputable section

structure Closed (M : Set Oracle) : Prop where
  lower : ∀ {A B}, B ∈ M → Reduces A B → A ∈ M
  join : ∀ {A B}, A ∈ M → B ∈ M → TuringRigidity.join A B ∈ M
  omega : ∀ {A}, A ∈ M → omegaJump A ∈ M

theorem Closed.jump {M : Set Oracle} (hM : Closed M) {A : Oracle} (hA : A ∈ M) : jump A ∈ M := by
  have h := hM.lower (hM.omega hA) (CodingExtraction.column_projection_reduces (omegaJump A) 1)
  change columns (omegaJump A) 1 ∈ M at h
  simpa only [omegaJump_column,OracleJump.iterate] using h

theorem Closed.iterate {M : Set Oracle} (hM : Closed M) {A : Oracle} (hA : A ∈ M) (n : ℕ) :
    OracleJump.iterate A n ∈ M := by
  induction n with
  | zero => exact hA
  | succ n ih => exact hM.jump ih

theorem Closed.presentation {M : Set Oracle} (hM : Closed M) {A : Oracle} (hA : A ∈ M) :
    JumpIdealPresentation.presentation A ∈ M := by
  obtain ⟨k,hk⟩ := presentation_bounded A
  exact hM.lower (hM.iterate (hM.omega hA) k) hk

theorem graph_mem {M : Set Oracle} (hM : Closed M) {I : CountableIdeal} {A : Oracle}
    (hA : Presented I A) (hAM : A ∈ M) (ρ : I ≃o I)
    (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    graphOracle hA ρ ∈ M :=
  hM.lower (hM.iterate hAM 11) (graphOracle_reduces hA ρ (source_4_1_8 ρ hp hz hA).2)

theorem extension_witnesses {M : Set Oracle} (hM : Closed M)
    {I : CountableIdeal} {A R : Oracle} (hA : Presented I A) (hAM : A ∈ M)
    (ρ : I ≃o I) (hp : Persistent I ρ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v)
    {X : Oracle} (hX : X ∈ M) :
    ∃ H ∈ M, ∃ S ∈ M, JumpCode H ∧ Includes A H ∧
      (∃ n, degree X = degree (columns H n)) ∧
      Action H (fun v => S v = true) ∧
      Compatible A H (fun v => R v = true) (fun v => S v = true) := by
  let B := join A X
  let J := JumpIdeal.generated (degree B)
  let H := JumpIdealPresentation.presentation B
  have hH : Presented J H := presents B
  have hHM : H ∈ M := hM.presentation (hM.join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := by
    intro y hy
    obtain ⟨n,rfl⟩ := (hA y).mp hy
    exact J.lower ((CodingExtraction.column_projection_reduces A n).trans
      (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ,he,hpσ⟩ := PersistentExtension.source_4_1_10 I J ρ hp hz hIJ (JumpIdeal.closed _)
  let S := graphOracle hH σ
  have hSM : S ∈ M := graph_mem hM hH hHM σ hpσ (hIJ hz)
  have hS : ∀ v, S v = true ↔ Graph σ hH v := fun v => by simp [S,graphOracle]
  obtain ⟨n,hn⟩ := (hH _).mp hXJ
  refine ⟨H,hHM,S,hSM,code_of_ideal hH (JumpIdeal.closed _),
    (includes_iff hA hH).mpr hIJ,⟨n,hn.symm⟩,
    (PersistenceCriterion.action_congr hS).mpr (action_of_automorphism hH σ),?_⟩
  intro i j n m hr hs hin
  exact ((compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
    ((hR _).mp hr) ((hS _).mp hs) hin

end
end TuringRigidity.PersistenceRealClosure

end OAI
