/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTModelBridge.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTPersistentDecoding
public import LeanPool.TuringConeRigidity.Representation.SetAutomorphismReconstruction

/-!
# Source TModel Bridge
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation OracleJump
universe u

noncomputable def modelDegreeEnv (R I F : ZFSet.{u}) : ℕ → ZFSet.{u} :=
  cons ZFSet.omega (cons (degreeUniverse R) (cons (degreeOrder R) (cons I (fun _ => F))))

theorem sourceT_arbitrary_persistent_graph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {J : CountableIdeal} {A : Oracle} (hA : Presented J A) (hAM : A ∈ modelReals M)
    (ρ : J ≃o J) (hp : Persistent J ρ) (hz : degree (jump FixedArithmetic.zero) ∈ J.carrier)
    (F : ZFSet.{u}) (hshape : F ⊆ ZFSet.prod (presentationSet R A) (presentationSet R A))
    (hF : ∀ x y : J, ZFSet.pair (presentedDegreeCode R hA x) (presentedDegreeCode R hA y) ∈ F ↔ ρ
      x = y) :
    F ∈ M ∧ (LevySigma.persistent 0 1 2 3 4).Realize M (modelDegreeEnv R (presentationSet R A) F)
      := by
  have hc : ∀ n, realCode (columns A n) ∈ R := fun n => (hR _).mpr (sourceT_real_column M hM hT
    hAM n)
  have hg : ∀ v, PersistentCountability.graphOracle hA ρ v = true ↔ Graph ρ hA v := by
    intro v; simp [PersistentCountability.graphOracle]
  have hEq := presentationGraph_unique R hA hc ρ hg F hshape hF
  have hFM : F ∈ M := hEq.symm ▸ (sourceT_persistent_graph_set M hM hT R hRM hR hRd hA hAM ρ hp
    hz).1
  refine ⟨hFM,?_⟩
  have he : ∀ i, modelDegreeEnv R (presentationSet R A) F i ∈ M := by
    intro i
    rcases i with _ | i
    · exact sourceT_omega_mem M hM hT
    rcases i with _ | i
    · exact internal_degreeUniverse M hM hT R hRM hRd
    rcases i with _ | i
    · exact internal_degreeOrder M hM hT R hRM hRd
    rcases i with _ | i
    · exact internal_presentationSet M hM hT R hRM hR hRd hAM
    exact hFM
  apply (LevySigma.realize_persistent M hM 0 1 2 3 4 _ he rfl).mpr
  change ModelPersistent M (degreeUniverse R) (degreeOrder R) (presentationSet R A) F
  rw [hEq]
  exact sourceT_presentation_modelPersistent M hM hT R hRM hR hRd hA hAM ρ hp hz

theorem source_4_2_4_4_2_5_transitive (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ R ∈ M, degreeUniverse R ∈ M ∧ degreeOrder R ∈ M ∧
      ∀ I ∈ M,
        (Formula.setIdeal 1 2 3).Realize M (modelDegreeEnv R I I) →
        (LevySigma.countable 0 3).Realize M (modelDegreeEnv R I I) →
        degreeCode R (jump FixedArithmetic.zero) ∈ I →
        ∃ J : CountableIdeal, ∃ A ∈ modelReals M, ∃ hA : Presented J A,
          presentationSet R A = I ∧
          (Function.Injective (presentedDegreeCode R hA)) ∧
          (∀ D ∈ I, ∃ x : J, presentedDegreeCode R hA x = D) ∧
          (∀ x y : J, ZFSet.pair (presentedDegreeCode R hA x) (presentedDegreeCode R hA y) ∈
            degreeOrder R ↔ x ≤ y) ∧
          ∀ F : ZFSet.{u}, SetAutomorphism I (degreeOrder R) F →
            ∃ ρ : J ≃o J,
              (∀ x y : J, ZFSet.pair (presentedDegreeCode R hA x) (presentedDegreeCode R hA y) ∈ F
                ↔ ρ x = y) ∧
              (Persistent J ρ → F ∈ M ∧ (LevySigma.persistent 0 1 2 3 4).Realize M (modelDegreeEnv
                R I F)) := by
  obtain ⟨R,hRM,hR,hRd'⟩ := internal_real_power M hM hT
  have hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w := fun w hw => by
    obtain ⟨B,_,hB⟩ := hRd' w hw; exact ⟨B,hB⟩
  have hU := internal_degreeUniverse M hM hT R hRM hRd
  have hL := internal_degreeOrder M hM hT R hRM hRd
  refine ⟨R,hRM,hU,hL,?_⟩
  intro I hIM hIf hcf hz
  have he : ∀ i, modelDegreeEnv R I I i ∈ M := by
    intro i
    rcases i with _ | i
    · exact sourceT_omega_mem M hM hT
    rcases i with _ | i
    · exact hU
    rcases i with _ | i
    · exact hL
    rcases i with _ | i
    · exact hIM
    exact hIM
  have hI := (Formula.realize_setIdeal M hM 1 2 3 _ he).mp hIf
  have hc := (LevySigma.realize_countable M hM 0 3 _ he rfl).mp hcf
  obtain ⟨J,A,hAM,hA,hAI⟩ := sourceT_countable_ideal_presentation M hM hT R hR hRd hIM hI hc
  have hcA : ∀ n, realCode (columns A n) ∈ R := fun n => (hR _).mpr (sourceT_real_column M hM hT
    hAM n)
  have hzJ : degree (jump FixedArithmetic.zero) ∈ J.carrier := (hA _).mpr
    ((degreeCode_mem_presentationSet R A hcA _).mp (hAI.symm ▸ hz))
  refine ⟨J,A,hAM,hA,hAI,presentedDegreeCode_injective R hA hcA,?_,presentedDegreeCode_order R hA
    hcA,?_⟩
  · intro D hD
    exact presentedDegreeCode_onto R hA hcA D (hAI.symm ▸ hD)
  · intro F hF
    have hFa : SetAutomorphism (presentationSet R A) (degreeOrder R) F := hAI.symm ▸ hF
    obtain ⟨ρ,hρ⟩ := setAutomorphism_reconstruct R hA hcA F hFa
    refine ⟨ρ,hρ,fun hp => ?_⟩
    have h := sourceT_arbitrary_persistent_graph M hM hT R hRM hR hRd hA hAM ρ hp hzJ F
      (fun z hz => ZFSet.mem_prod.mpr (hFa.1.1 z hz)) hρ
    rwa [hAI] at h

end TuringRigidity.BoundedSetTheory

end OAI
