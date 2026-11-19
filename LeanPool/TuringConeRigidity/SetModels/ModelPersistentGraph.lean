/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelPersistentGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.PresentedDegreeEmbedding
public import LeanPool.TuringConeRigidity.SetModels.ModelPersistenceReals

/-!
# Model Persistent Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open PersistentCountability
open TransitiveNameModel EncodedForcing PersistentRestrictions PersistentPresentation OracleJump
universe u

theorem presentationGraph_function (R : ZFSet.{u}) {I : CountableIdeal} {H S : Oracle}
    (hH : Presented I H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (ρ : I ≃o I) (hS : ∀ v, S v = true ↔ Graph ρ hH v) :
    TransitiveNameModel.FunctionGraph (presentationSet R H) (presentationSet R H)
      (presentationGraph R H S) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro D hD
    obtain ⟨x,rfl⟩ := presentedDegreeCode_onto R hH hc D hD
    refine ⟨presentedDegreeCode R hH (ρ x),presentedDegreeCode_mem R hH (ρ x),
      (presentationGraph_actual R hH hc ρ hS x (ρ x)).mpr rfl,?_⟩
    intro F hF hDF
    obtain ⟨y,rfl⟩ := presentedDegreeCode_onto R hH hc F hF
    exact congrArg (presentedDegreeCode R hH) ((presentationGraph_actual R hH hc ρ hS x y).mp
      hDF).symm

theorem presentationGraph_onto (R : ZFSet.{u}) {I : CountableIdeal} {H S : Oracle}
    (hH : Presented I H) (hc : ∀ n, realCode (columns H n) ∈ R)
    (ρ : I ≃o I) (hS : ∀ v, S v = true ↔ Graph ρ hH v) :
    ∀ F ∈ presentationSet R H, ∃ D ∈ presentationSet R H, ZFSet.pair D F ∈ presentationGraph R H S
      := by
  intro F hF
  obtain ⟨y,rfl⟩ := presentedDegreeCode_onto R hH hc F hF
  refine ⟨presentedDegreeCode R hH (ρ.symm y),presentedDegreeCode_mem R hH (ρ.symm y),?_⟩
  exact (presentationGraph_actual R hH hc ρ hS (ρ.symm y) y).mpr (ρ.apply_symm_apply y)

theorem sourceT_persistent_graph_set (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M)
    (hRd : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    {I : CountableIdeal} {H : Oracle} (hH : Presented I H) (hHM : H ∈ modelReals M)
    (ρ : I ≃o I) (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier) :
    presentationGraph R H (graphOracle hH ρ) ∈ M ∧
      TransitiveNameModel.FunctionGraph (presentationSet R H) (presentationSet R H)
        (presentationGraph R H (graphOracle hH ρ)) ∧
      ∀ x y : I, ZFSet.pair (presentedDegreeCode R hH x) (presentedDegreeCode R hH y) ∈
        presentationGraph R H (graphOracle hH ρ) ↔ ρ x = y := by
  have hc : ∀ n, realCode (columns H n) ∈ R :=
    fun n => (hR _).mpr (sourceT_real_column M hM hT hHM n)
  have hS : ∀ v, graphOracle hH ρ v = true ↔ Graph ρ hH v := by
    intro v; simp [graphOracle]
  exact ⟨internal_presentationGraph M hM hT R hRM hR hRd hHM
      (sourceT_persistent_graph_real M hM hT hH hHM ρ hp hz),
    presentationGraph_function R hH hc ρ hS,presentationGraph_actual R hH hc ρ hS⟩

end TuringRigidity.BoundedSetTheory

end OAI
