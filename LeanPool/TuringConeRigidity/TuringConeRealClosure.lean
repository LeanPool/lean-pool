/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeRealClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeArithmeticCriterion
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceRealClosure

/-!
# Persistent cone graphs in arithmetically closed real collections

The graph of a persistent map is already in any appropriately closed real
collection containing its column presentation. Persistent extensions with both
presentation and graph in that same collection are obtained without a global
cone isomorphism. These are the witnesses needed for internal persistence.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeRealClosure

open EncodedForcing OracleJump PersistentRestrictions ConePersistence ConePresentation
open NumericalIdeal NumericalExtension

noncomputable section

theorem graph_mem {M : Set Oracle} (hM : PersistenceRealClosure.Closed M)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ M)
    {a : Degree} (ρ : I ≃o Cone I a) (hp : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) : graphOracle hA ρ ∈ M :=
  hM.lower (hM.iterate hAM 11) (graphOracle_reduces hA ρ
    (ConePersistentLocality.arithmetic_presentation_of_persistent ρ hp hA hza).2)

/-- Extension presentations and graph codes can be chosen in the closed real
collection. In particular, ambient choice does not substitute for internal
availability of these witnesses. -/
theorem extension_witnesses {M : Set Oracle} (hM : PersistenceRealClosure.Closed M)
    {I : CountableIdeal} {A B R : Oracle} (hA : Presented I A) (hAM : A ∈ M)
    (ρ : I ≃o Cone I (degree B)) (hp : ConePersistence.Persistent I ρ)
    (hza : degreeJump (degree B) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v) {X : Oracle} (hX : X ∈ M) :
    ∃ H ∈ M, ∃ S ∈ M, JumpCode H ∧ Includes A H ∧
      (∃ n, degree X = degree (columns H n)) ∧
      ConeNumerical.Action B H (fun v => S v = true) ∧
      Compatible A H (fun v => R v = true) (fun v => S v = true) := by
  let C := join A X
  let J := JumpIdeal.generated (degree C)
  let H := JumpIdealPresentation.presentation C
  have hH : Presented J H := JumpIdealPresentation.presents C
  have hHM : H ∈ M := hM.presentation (hM.join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := fun y hy =>
    J.lower ((presentation_bound hA hy).trans (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ, he, hpσ⟩ := ConePersistentExtension.persistent_extension I J ρ hp hza hIJ
    (JumpIdeal.closed _)
  let S := graphOracle hH σ
  have hSM : S ∈ M := graph_mem hM hH hHM σ hpσ (hIJ hza)
  have hS : ∀ v, S v = true ↔ Graph σ hH v := fun v => by simp [S, graphOracle]
  obtain ⟨n, hn⟩ := (hH _).mp hXJ
  refine ⟨H, hHM, S, hSM, code_of_ideal hH (JumpIdeal.closed _),
    (includes_iff hA hH).mpr hIJ, ⟨n, hn.symm⟩,
    (ConeNumerical.action_congr hS).mpr (ConeNumerical.action_of_iso hH σ), ?_⟩
  intro i j n m hr hs hin
  exact ((ConeNumerical.compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
    ((hR _).mp hr) ((hS _).mp hs) hin

end
end OAI.TuringRigidity.ConeRealClosure
