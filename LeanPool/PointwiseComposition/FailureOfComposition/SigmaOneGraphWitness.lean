/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneSemidecisionCore
public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneSearch

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Extracting an output from a semidecision program for a functional arithmetic
graph. The search ranges over candidate outputs together with computation
stages, so divergent rejected candidates do not block later outputs.
-/

@[expose] public section

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition
namespace SigmaOneRealization

open ProgramGraph ArithmeticCodeCompiler

/-- Convert a candidate/input pair into the graph's input/output vector. -/
def reorderProgram (c : PCode) : PCode :=
  .comp c (.pair .right (.pair .left .zero))

/-- Search the graph semidecision program and return its successful output. -/
def graphProgram (c : PCode) : PCode :=
  SigmaOneSearch.candidateSearch (reorderProgram c)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]

theorem computes_reorder (c : PCode) (x y z : M) :
    Computes (reorderProgram c) (pair y x) z ↔ Computes c (encodeVector ![x, y]) z :=
  by
  rw [reorderProgram, computes_comp]
  simp only [computes_pair, computes_left, computes_right, computes_zero, pi₁_pair, pi₂_pair]
  constructor
  · rintro ⟨w, ⟨a, b, rfl, ⟨d, e, rfl, rfl, rfl⟩, rfl⟩, h⟩
    simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ] using h
  · intro h
    refine ⟨pair x (pair y 0), ⟨x, pair y 0, rfl, ⟨y, 0, rfl, rfl, rfl⟩, rfl⟩, ?_⟩
    simpa only [encodeVector, Matrix.cons_val_zero, Matrix.cons_val_succ] using h

/-- A semidecision program for a PA-functional graph yields an actual program
whose graph PA proves uniformly equivalent to the original graph. -/
theorem realize_of_semidecides (F : ProofSearch.Graph) (hF : ProofSearch.Functional F)
    (c : PCode) (hc : Semidecides F.val c) :
    ProofSearch.Uniform 𝐏𝐀 (ConcreteEvaluator.eventualGraph (encode (graphProgram c))) F :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hf : V↓[ℒₒᵣ] ⊧ ProofSearch.functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) V inferInstance
  rw [models_iff, ProofSearch.functionalSentence_eval] at hf
  rw [models_iff, ProofSearch.uniformSentence_eval]
  intro x y
  change
    Computes (SigmaOneSearch.candidateSearch (reorderProgram c)) x y ↔
      Semiformula.Evalb ![x, y] F.val
  have hrel (a : V) :
    Computes (reorderProgram c) (pair a x) 0 ↔ Semiformula.Evalb ![x, a] F.val :=
    by
    rw [computes_reorder, hc V ![x, a] 0]
    simp
  have hu :
    ∀ a b : V,
      Computes (reorderProgram c) (pair a x) 0 →
        Computes (reorderProgram c) (pair b x) 0 → a = b :=
    by
    intro a b ha hb
    exact hf x a b ((hrel a).mp ha) ((hrel b).mp hb)
  exact (SigmaOneSearch.candidateSearch_of_functional (reorderProgram c) x y hu).trans (hrel y)

end SigmaOneRealization
end FailureOfComposition

end

end PointwiseComposition
