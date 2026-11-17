/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeModelGraphs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeSetGraphs
public import LeanPool.TuringConeRigidity.SetModels.CountedRealsPresentation
public import LeanPool.TuringConeRigidity.TuringConeRealClosure

/-!
# Persistent cone graphs inside models

Internal real codes are converted to native ZFSet graphs. The hypotheses on a
model are the weak Context used by the original collapse argument; Choice
inside the model is not assumed. In particular these lemmas apply inside the
collapse extensions used for descent to L(R).
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeModelGraphs

open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetModelSyntax SetModelArithmetic SetDegreeDecoding
open PersistentRestrictions ConePersistence ConePresentation ConeSetGraphs
open OracleJump

universe u
noncomputable section

/-- The entire set graph is internal, not just each of its pairs. -/
theorem persistent_sets {M : ZFSet.{u}} (C : Context M)
    {I : CountableIdeal} {a : Degree} {A : Oracle}
    (hA : ConePresentation.Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o Cone I a) (hρ : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) :
    idealSet I ∈ M ∧ coneGraph ρ ∈ M := by
  obtain ⟨E, hE, hEc⟩ := internal_degreeEquality_graph C
  have hC := realClosure C
  let G := ConePresentation.graphOracle hA ρ
  have hGM : G ∈ reals M := ConeRealClosure.graph_mem hC hA hAM ρ hρ hza
  have hG : ∀ v, G v = true ↔ ConePresentation.Graph ρ hA v :=
    fun v => by simp [G, ConePresentation.graphOracle]
  exact coded_sets M C.transitive C.pairing C.union C.power C.separation C.infinity hC
    C.pairing_mem pairingSet_code hE hEc hA hAM ρ hGM hG

/-- Counting the old real family supplies an internal presentation, so the
arithmetic graph bound reconstructs the entire persistent cone graph. -/
theorem persistent_mem_of_counted_reals {M R : ZFSet.{u}} (C : Context M) (hR : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, realSet B = x)
    (hcount : BoundedSetTheory.InternallyCountable M R) (I : CountableIdeal)
    (hI : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, realSet B ∈ R ∧ degree B = d)
    {a : Degree} (ρ : I ≃o Cone I a) (hρ : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) : coneGraph ρ ∈ M := by
  obtain ⟨A, hAM, hA⟩ := SetModelCountability.presentation_of_counted_reals
    C hR hreal hcount I hI
  exact (persistent_sets C hA hAM ρ hρ hza).2

/-- Persistent extensions with both their ideal and full graph inside the
model, for any requested internal real. -/
theorem persistent_extension_sets {M : ZFSet.{u}} (C : Context M)
    {I : CountableIdeal} {a : Degree} {A : Oracle}
    (hA : ConePresentation.Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o Cone I a) (hρ : ConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o Cone J a) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ ConePersistence.Extends hIJ ρ σ ∧
      ConePersistence.Persistent J σ ∧ idealSet J ∈ M ∧ coneGraph σ ∈ M := by
  let B := join A X
  let J := JumpIdeal.generated (degree B)
  let H := JumpIdealPresentation.presentation B
  have hH : ConePresentation.Presented J H := JumpIdealPresentation.presents B
  have hC := realClosure C
  have hHM : H ∈ reals M := hC.presentation (hC.join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := fun y hy =>
    J.lower ((presentation_bound hA hy).trans (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ, he, hσ⟩ := ConePersistentExtension.persistent_extension I J ρ hρ hza hIJ
    (JumpIdeal.closed _)
  have hsets := persistent_sets C hH hHM σ hσ (hIJ hza)
  exact ⟨J, σ, hIJ, hXJ, he, hσ, hsets⟩

end
end OAI.TuringRigidity.ConeModelGraphs
