/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteIndexObstruction
public import LeanPool.PointwiseComposition.FailureOfComposition.SigmaOneRealization
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteAdequacy

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The range partial identity of a Sigma-one graph and its realization by an index
of the fixed evaluator. The defining range equation holds in every PA model.
PA-uniformly equivalent choices of realizing indices are pointwise equivalent
over every PA extension.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace ConcreteIndices

open ProofSearch ConcreteEvaluator ProgramIndices

/-- The partial identity on the range of a Sigma-one graph. -/
def rangeOfGraph (F : Graph) : Graph :=
  .mkSigma (“r w. r = w ∧ ∃ x, !F.val x r”)

@[simp]
theorem rangeOfGraph_eval {M : Type*} [ORingStructure M] (F : Graph) (v : Fin 2 → M) :
    (rangeOfGraph F).val.Evalb v ↔ v 0 = v 1 ∧ ∃ x : M, F.val.Evalb ![x, v 0] := by
  simp [rangeOfGraph]

/-- Range partial identities are PA-provably functional, even if the source
graph has not been assumed functional. -/
theorem rangeOfGraph_functional (F : Graph) : Functional (rangeOfGraph F) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact ((rangeOfGraph_eval F _).mp hy).1.symm.trans ((rangeOfGraph_eval F _).mp hz).1

/-- PA-uniform graph equality is preserved by taking the range partial identity. -/
theorem uniform_rangeOfGraph {F G : Graph} (h : Uniform 𝐏𝐀 F G) :
    Uniform 𝐏𝐀 (rangeOfGraph F) (rangeOfGraph G) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have heq := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  simp only [models_iff, uniformSentence_eval] at heq ⊢
  intro r w
  simp only [rangeOfGraph_eval, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact and_congr_right fun _ => exists_congr fun x => heq x r

/-- The range partial identity of a program in the fixed evaluator. -/
def rangeGraph (e : ℕ) : Graph :=
  rangeOfGraph (eventualGraph e)

@[simp]
theorem rangeGraph_eval {M : Type*} [ORingStructure M] (e : ℕ) (v : Fin 2 → M) :
    (rangeGraph e).val.Evalb v ↔ v 0 = v 1 ∧ ∃ x : M, (eventualGraph e).val.Evalb ![x, v 0] :=
  rangeOfGraph_eval (eventualGraph e) v

theorem rangeGraph_functional (e : ℕ) : Functional (rangeGraph e) :=
  rangeOfGraph_functional (eventualGraph e)

/-- Choose a range program using the proved Sigma-one graph realization theorem. -/
noncomputable def rangeIndex (e : ℕ) : ℕ :=
  Classical.choose (SigmaOneRealization.realize_graph (rangeGraph e) (rangeGraph_functional e))

theorem rangeIndex_realizes (e : ℕ) :
    Uniform 𝐏𝐀 (eventualGraph (rangeIndex e)) (rangeGraph e) :=
  Classical.choose_spec
    (SigmaOneRealization.realize_graph (rangeGraph e) (rangeGraph_functional e))

/-- The selected range index satisfies the defining equation in every PA model. -/
theorem rangeIndex_graph_equation {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (e : ℕ)
    (r w : M) :
    (eventualGraph (rangeIndex e)).val.Evalb ![r, w] ↔
      r = w ∧ ∃ x : M, (eventualGraph e).val.Evalb ![x, r] :=
  by
  have h := consequence_iff.mp (Theory.Proof.sound (rangeIndex_realizes e)) M inferInstance
  simp only [models_iff, uniformSentence_eval] at h
  exact (h r w).trans (rangeGraph_eval e _)

/-- In the standard model this is the partial identity on the program's range. -/
theorem rangeIndex_eval (e r w : ℕ) :
    w ∈ Kleene.eval (rangeIndex e) r ↔ r = w ∧ ∃ x : ℕ, r ∈ Kleene.eval e x :=
  by
  rw [← eventualGraph_adequate]
  simpa only [eventualGraph_adequate] using rangeIndex_graph_equation e r w

/-- A PA-uniform description of a source graph transports to its selected range. -/
theorem rangeIndex_of_uniform {e : ℕ} {F : Graph} (h : Uniform 𝐏𝐀 (eventualGraph e) F) :
    Uniform 𝐏𝐀 (eventualGraph (rangeIndex e)) (rangeOfGraph F) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have heq := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  simp only [models_iff, uniformSentence_eval] at heq ⊢
  intro r w
  rw [rangeIndex_graph_equation, rangeOfGraph_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact and_congr_right fun _ => exists_congr fun x => heq x r

/-- The empty graph has empty range in PA. -/
theorem rangeOfGraph_empty : Uniform 𝐏𝐀 (rangeOfGraph empty) empty :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  simp [models_iff, uniformSentence_eval]

/-- The selected range of the concrete empty program is uniformly empty in PA. -/
theorem rangeIndex_empty :
    Uniform 𝐏𝐀 (eventualGraph (rangeIndex ConcreteEmptyGraph.concreteEmptyIndex)) empty :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have hempty := consequence_iff.mp (Theory.Proof.sound eventualGraph_empty) M inferInstance
  simp only [models_iff, uniformSentence_eval, empty_eval] at hempty ⊢
  intro r w
  rw [rangeIndex_graph_equation]
  simp only [hempty, exists_false, and_false]

/-- Any two indices realizing the same range graph are PA-uniformly equivalent. -/
theorem rangeIndex_realization_unique {e r s : ℕ}
    (hr : Uniform 𝐏𝐀 (eventualGraph r) (rangeGraph e))
    (hs : Uniform 𝐏𝐀 (eventualGraph s) (rangeGraph e)) :
    Uniform 𝐏𝐀 (eventualGraph r) (eventualGraph s) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have hr' := consequence_iff.mp (Theory.Proof.sound hr) M inferInstance
  have hs' := consequence_iff.mp (Theory.Proof.sound hs) M inferInstance
  simp only [models_iff, uniformSentence_eval] at hr' hs' ⊢
  exact fun x y => (hr' x y).trans (hs' x y).symm

/-- Replacing the selected range index by any PA-uniform realization leaves its
pointwise class unchanged over every PA extension. -/
theorem rangeIndex_choice_independent (T : ArithmeticTheory) [𝐏𝐀 ≼ T] {e r : ℕ}
    (hr : Uniform 𝐏𝐀 (eventualGraph r) (rangeGraph e)) : PointwiseIndex T r (rangeIndex e) :=
  (pointwiseIndex_iff T r (rangeIndex e)).mpr
    (uniform_to_pointwise T (rangeIndex_realization_unique hr (rangeIndex_realizes e)))

end ConcreteIndices
end FailureOfComposition

end

end PointwiseComposition
