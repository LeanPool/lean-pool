/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTPersistentDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelPersistenceSatisfaction

/-!
# Source TPersistent Decoding
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation OracleJump
open NumericalIdeal NumericalAutomorphism NumericalExtension
universe u

theorem sourceT_presentation_modelPersistent (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ modelReals M)
    (ρ : I ≃o I) (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    ModelPersistent M (degreeUniverse R) (degreeOrder R) (presentationSet R A)
      (presentationGraph R A (PersistentCountability.graphOracle hA ρ)) := by
  let G := PersistentCountability.graphOracle hA ρ
  have hG : ∀ v, G v = true ↔ Graph ρ hA v := by
    intro v; simp [G, PersistentCountability.graphOracle]
  have hcA : ∀ n, realCode (columns A n) ∈ R := fun n => (hR _).mpr (sourceT_real_column M hM hT
    hAM n)
  refine ⟨presentationGraph_automorphism R hA hcA ρ hG,?_⟩
  intro D hD
  obtain ⟨X,hX,rfl⟩ := (mem_degreeUniverse R D).mp hD
  obtain ⟨H,hHM,S,hSM,hJ,hin,hXH,ha,hcompat⟩ :=
    sourceT_persistent_extension_reals M hM hT hA hAM ρ hp hz hG ((hR X).mp hX)
  have hH := decoded_presentation H hJ
  have hcH : ∀ n, realCode (columns H n) ∈ R := fun n => (hR _).mpr (sourceT_real_column M hM hT
    hHM n)
  obtain ⟨hJM,E,hEM,hE,honto⟩ := internal_presentation_countable M hM hT R hRM hR hRd hHM
  refine ⟨presentationSet R H,hJM,presentationGraph R H S,
    internal_presentationGraph M hM hT R hRM hR hRd hHM hSM,E,hEM,
    presentationSet_ideal R hH hcH,⟨hE,honto⟩,presentationGraph_action R hH hcH ha,
    presentationSet_subset_of_includes R hcA hin,?_,
    presentationGraph_subset_of_compatible R hcA hin ha hcompat⟩
  obtain ⟨n,hn⟩ := hXH
  exact (mem_presentationSet R H _).mpr ⟨n,(degreeCode_equal R hX).mpr hn⟩

theorem sourceT_persistent_decoding (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {I : ZFSet.{u}} (hIM : I ∈ M)
    (hI : SetIdeal (degreeUniverse R) (degreeOrder R) I) (hcount : InternallyCountable M I)
    (hz : degreeCode R (jump FixedArithmetic.zero) ∈ I) :
    ∃ J : CountableIdeal, ∃ A ∈ modelReals M, ∃ hA : Presented J A, presentationSet R A = I ∧
      ∀ ρ : J ≃o J, Persistent J ρ →
        let F := presentationGraph R A (PersistentCountability.graphOracle hA ρ)
        F ∈ M ∧ ModelPersistent M (degreeUniverse R) (degreeOrder R) I F := by
  obtain ⟨J,A,hAM,hA,hAI⟩ := sourceT_countable_ideal_presentation M hM hT R hR hRd hIM hI hcount
  have hcA : ∀ n, realCode (columns A n) ∈ R := fun n => (hR _).mpr (sourceT_real_column M hM hT
    hAM n)
  have hzJ : degree (jump FixedArithmetic.zero) ∈ J.carrier := by
    apply (hA _).mpr
    exact (degreeCode_mem_presentationSet R A hcA _).mp (hAI.symm ▸ hz)
  refine ⟨J,A,hAM,hA,hAI,?_⟩
  intro ρ hp
  refine ⟨(sourceT_persistent_graph_set M hM hT R hRM hR hRd hA hAM ρ hp hzJ).1,?_⟩
  rw [←hAI]
  exact sourceT_presentation_modelPersistent M hM hT R hRM hR hRd hA hAM ρ hp hzJ

theorem sourceT_internal_degrees_and_decoding (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ R ∈ M, (∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M) ∧
      degreeUniverse R ∈ M ∧ degreeOrder R ∈ M ∧
      ∀ I ∈ M, SetIdeal (degreeUniverse R) (degreeOrder R) I → InternallyCountable M I →
        degreeCode R (jump FixedArithmetic.zero) ∈ I →
        ∃ J : CountableIdeal, ∃ A ∈ modelReals M, ∃ hA : Presented J A, presentationSet R A = I ∧
          ∀ ρ : J ≃o J, Persistent J ρ →
            let F := presentationGraph R A (PersistentCountability.graphOracle hA ρ)
            F ∈ M ∧ ModelPersistent M (degreeUniverse R) (degreeOrder R) I F := by
  obtain ⟨R,hRM,hR,hRd⟩ := internal_real_power M hM hT
  have hd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w := fun w hw => by
    obtain ⟨B,_,hB⟩ := hRd w hw; exact ⟨B,hB⟩
  exact ⟨R,hRM,hR,internal_degreeUniverse M hM hT R hRM hd,internal_degreeOrder M hM hT R hRM hd,
    fun I hIM hI hc hz => sourceT_persistent_decoding M hM hT R hRM hR hd hIM hI hc hz⟩

end TuringRigidity.BoundedSetTheory

end OAI
