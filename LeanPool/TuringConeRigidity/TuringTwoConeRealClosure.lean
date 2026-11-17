/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeRealClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeArithmeticCriterion
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceRealClosure

/-!
# Internal availability of two-cone graph codes

Eleven-jump graph bounds put every persistent graph into an arithmetically
closed real collection containing its presentation. Extension witnesses have
both their presentation and their conventional graph in the same collection.
This is not inferred merely from ambient choice.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeRealClosure

open EncodedForcing OracleJump PersistentRestrictions
open ConePersistence (Cone)
open ConePresentation (Presented)
open TwoConePresentation (RawGraph)
open TwoConeNumerical (graphOracle graphOracle_reduces)
open NumericalIdeal NumericalExtension

noncomputable section

theorem graph_mem {M : Set Oracle} (hM : PersistenceRealClosure.Closed M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ M)
    {a b : Degree} (ρ : Cone I a ≃o Cone I b) (hp : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    graphOracle ρ A ∈ M :=
  hM.lower (hM.iterate hAM 11) (graphOracle_reduces ρ
    (TwoConePresentation.raw_graph_arithmetic_of_persistent ρ hp hA hza hzb).2)

/-- Both the extension presentation and its actual graph code are internal. -/
theorem extension_witnesses {M : Set Oracle} (hM : PersistenceRealClosure.Closed M)
    {I : CountableIdeal} {A B C R : Oracle} (hA : Presented I A) (hAM : A ∈ M)
    (ρ : Cone I (degree B) ≃o Cone I (degree C)) (hp : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump (degree B) ∈ I.carrier)
    (hzb : degreeJump (degree C) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ RawGraph ρ A v) {X : Oracle} (hX : X ∈ M) :
    ∃ H ∈ M, ∃ S ∈ M, JumpCode H ∧ Includes A H ∧
      (∃ n, degree X = degree (columns H n)) ∧
      TwoConeNumerical.Action B C H (fun v => S v = true) ∧
      Compatible A H (fun v => R v = true) (fun v => S v = true) := by
  let D := join A X
  let J := JumpIdeal.generated (degree D)
  let H := JumpIdealPresentation.presentation D
  have hH : Presented J H := JumpIdealPresentation.presents D
  have hHM : H ∈ M := hM.presentation (hM.join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := fun y hy =>
    J.lower ((ConePresentation.presentation_bound hA hy).trans (reduces_join_left A X))
      (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ, he, hpσ⟩ := TwoConePersistentExtension.persistent_extension I J ρ hp
    hza hzb hIJ (JumpIdeal.closed _)
  let S := graphOracle σ H
  have hSM : S ∈ M := graph_mem hM hH hHM σ hpσ (hIJ hza) (hIJ hzb)
  have hS : ∀ v, S v = true ↔ RawGraph σ H v := fun v => TwoConeNumerical.graphOracle_true σ H v
  obtain ⟨n, hn⟩ := (hH _).mp hXJ
  refine ⟨H, hHM, S, hSM, code_of_ideal hH (JumpIdeal.closed _),
    (includes_iff hA hH).mpr hIJ, ⟨n, hn.symm⟩,
    (TwoConeNumerical.action_congr hS).mpr (TwoConeNumerical.action_of_iso hH σ), ?_⟩
  intro i j n m hr hs hin
  exact ((TwoConeNumerical.compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
    ((hR _).mp hr) ((hS _).mp hs) hin

end
end OAI.TuringRigidity.TwoConeRealClosure
