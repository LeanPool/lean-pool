/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeModelGraphs.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeSetGraphs
public import LeanPool.TuringConeRigidity.SetModels.CountedRealsPresentation
public import LeanPool.TuringConeRigidity.TuringTwoConeRealClosure

/-!
# Persistent two-cone graphs inside models

The whole set graph is reconstructed using internal real codes. The Context
is the weak theory from the original collapse argument; internal Choice is
not assumed. Both base jumps are explicit where arithmetic presentation is
used. The source cone is not silently replaced by the entire ideal.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeModelGraphs

open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetModelSyntax SetModelArithmetic SetDegreeDecoding
open PersistentRestrictions OracleJump
open ConePersistence (Cone)
open ConePresentation (Presented presentation_bound)
open TwoConeSetGraphs

universe u
noncomputable section

/-- The entire graph is internal, not just each of its pairs. -/
theorem persistent_sets {M : ZFSet.{u}} (C : Context M)
    {I : CountableIdeal} {a b : Degree} {A : Oracle}
    (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : Cone I a ≃o Cone I b) (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    idealSet I ∈ M ∧ coneGraph ρ ∈ M := by
  obtain ⟨E, hE, hEc⟩ := internal_degreeEquality_graph C
  have hC := realClosure C
  let G := TwoConeNumerical.graphOracle ρ A
  have hGM : G ∈ reals M := TwoConeRealClosure.graph_mem hC hA hAM ρ hρ hza hzb
  have hG : ∀ v, G v = true ↔ TwoConePresentation.RawGraph ρ A v :=
    fun v => TwoConeNumerical.graphOracle_true ρ A v
  exact coded_sets M C.transitive C.pairing C.union C.power C.separation C.infinity hC
    C.pairing_mem pairingSet_code hE hEc hA hAM ρ hGM hG

/-- An internal enumeration of the old reals supplies an internal presentation. -/
theorem persistent_mem_of_counted_reals {M R : ZFSet.{u}} (C : Context M) (hR : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, realSet B = x)
    (hcount : BoundedSetTheory.InternallyCountable M R) (I : CountableIdeal)
    (hI : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, realSet B ∈ R ∧ degree B = d)
    {a b : Degree} (ρ : Cone I a ≃o Cone I b) (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier) :
    coneGraph ρ ∈ M := by
  obtain ⟨A, hAM, hA⟩ := SetModelCountability.presentation_of_counted_reals
    C hR hreal hcount I hI
  exact (persistent_sets C hA hAM ρ hρ hza hzb).2

/-- Persistent extensions with both ideal and whole graph inside the model. -/
theorem persistent_extension_sets {M : ZFSet.{u}} (C : Context M)
    {I : CountableIdeal} {a b : Degree} {A : Oracle}
    (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : Cone I a ≃o Cone I b) (hρ : TwoConePersistence.Persistent I ρ)
    (hza : degreeJump a ∈ I.carrier) (hzb : degreeJump b ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : Cone J a ≃o Cone J b) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ TwoConePersistence.Extends hIJ ρ σ ∧
      TwoConePersistence.Persistent J σ ∧ idealSet J ∈ M ∧ coneGraph σ ∈ M := by
  let B := join A X
  let J := JumpIdeal.generated (degree B)
  let H := JumpIdealPresentation.presentation B
  have hH : Presented J H := JumpIdealPresentation.presents B
  have hC := realClosure C
  have hHM : H ∈ reals M := hC.presentation (hC.join hAM hX)
  have hIJ : I.carrier ⊆ J.carrier := fun y hy =>
    J.lower ((presentation_bound hA hy).trans (reduces_join_left A X)) (JumpIdeal.includes _)
  have hXJ : degree X ∈ J.carrier := J.lower (reduces_join_right A X) (JumpIdeal.includes _)
  obtain ⟨σ, he, hσ⟩ := TwoConePersistentExtension.persistent_extension I J ρ hρ
    hza hzb hIJ (JumpIdeal.closed _)
  have hsets := persistent_sets C hH hHM σ hσ (hIJ hza) (hIJ hzb)
  exact ⟨J, σ, hIJ, hXJ, he, hσ, hsets⟩

end
end OAI.TuringRigidity.TwoConeModelGraphs
