/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcretePersistence
public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteEmptyGraph
public import LeanPool.PointwiseComposition.FailureOfComposition.ProofSearchTemplate

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The existential-stage graph of the repository's concrete evaluator.

Persistence of successful computations brings two possibly nonstandard stages
to a common stage. It therefore supplies PA proofs of functionality and of the
composition equation for the actual canonical composition indices.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition
namespace ConcreteEvaluator

open ProofSearch

noncomputable section

/-- PA proves persistence at each fixed standard index, with all stages,
inputs, and outputs quantified inside the arithmetic sentence. -/
theorem evaluator_persistence_provable (q : ℕ) :
    𝐏𝐀 ⊢
      (“∀ s t x y,
          s ≤ t →
            !evalnCertificateFormula.val s !!(q)x y →
              !evalnCertificateFormula.val t !!(q)x y”) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simpa [models_iff, numeral_eq_natCast] using
    (evalnCertificateFormula_natCode_persist (M := M) q)

/-- The graph at a fixed standard program index, allowing any internal stage. -/
def eventualGraph (q : ℕ) : Graph :=
  .mkSigma (“x y. ∃ s, !evalnCertificateFormula.val s !!(q)x y”)

@[simp]
theorem eventualGraph_eval {M : Type*} [ORingStructure M] (q : ℕ) (v : Fin 2 → M) :
    (eventualGraph q).val.Evalb v ↔
      ∃ s : M,
        Semiformula.Evalb ![s, (ORingStructure.numeral q : M), v 0, v 1]
          (evalnCertificateFormula : ArithmeticSemisentence 4) :=
  by simp [eventualGraph]

/-- Two successful computations of one standard index have the same output,
even when their stages are nonstandard and different. -/
theorem eventualGraph_output_unique {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (q : ℕ)
    (x y z : M) (hy : (eventualGraph q).val.Evalb ![x, y])
    (hz : (eventualGraph q).val.Evalb ![x, z]) : y = z :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp hy
  obtain ⟨t, ht⟩ := (eventualGraph_eval q _).mp hz
  simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
  have hs' := evalnCertificateFormula_natCode_persist q s (s + t) x y le_self_add hs
  have ht' := evalnCertificateFormula_natCode_persist q t (s + t) x z le_add_self ht
  exact
    add_right_cancel
      (eval_unique ((evalnCertificateFormula_eval_history_iff (s + t) (q : M) x y).mp hs')
        ((evalnCertificateFormula_eval_history_iff (s + t) (q : M) x z).mp ht'))

/-- Functionality is proved in PA for this concrete evaluator graph. -/
theorem eventualGraph_functional (q : ℕ) : Functional (eventualGraph q) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  exact eventualGraph_output_unique q

/-- The composition equation holds in every PA model at all internal inputs
and outputs; the two component computations need not start at the same stage. -/
theorem eventualGraph_comp_eval {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] (fCode gCode : ℕ)
    (x z : M) :
    (eventualGraph (canonicalPartrecCompIndex fCode gCode)).val.Evalb ![x, z] ↔
      ∃ y : M,
        (eventualGraph gCode).val.Evalb ![x, y] ∧ (eventualGraph fCode).val.Evalb ![y, z] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (eventualGraph_eval _ _).mp h
    obtain ⟨y, hy, hz⟩ :=
      evalnCertificateFormula_canonicalPartrecCompIndex_forward s x z fCode gCode hs
    exact ⟨y, (eventualGraph_eval _ _).mpr ⟨s, hy⟩, (eventualGraph_eval _ _).mpr ⟨s, hz⟩⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨s, hs⟩ := (eventualGraph_eval _ _).mp hy
    obtain ⟨t, ht⟩ := (eventualGraph_eval _ _).mp hz
    simp only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
    have hs' := evalnCertificateFormula_natCode_persist gCode s (s + t) x y le_self_add hs
    have ht' := evalnCertificateFormula_natCode_persist fCode t (s + t) y z le_add_self ht
    apply (eventualGraph_eval _ _).mpr
    refine ⟨s + t, ?_⟩
    apply evalnCertificateFormula_canonicalPartrecCompIndex_reverse (s + t) x y z fCode gCode
    · simpa only [numeral_eq_natCast_app] using hs'
    · simpa only [numeral_eq_natCast_app] using ht'

/-- PA proves relational composition for the concrete program indices. -/
theorem eventualGraph_composition (fCode gCode : ℕ) :
    Uniform 𝐏𝐀 (eventualGraph (canonicalPartrecCompIndex fCode gCode))
      (comp (eventualGraph fCode) (eventualGraph gCode)) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x z
  rw [comp_eval]
  exact eventualGraph_comp_eval fCode gCode x z

/-- The identity index already defined by Mathlib's program numbering realizes
the equality graph in PA, at all internal inputs and outputs. -/
theorem eventualGraph_identity : Uniform 𝐏𝐀 (eventualGraph Kleene.identityIndex) identity :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [identity_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hi : (eventualGraph Kleene.identityIndex).val.Evalb ![x, x] :=
    by
    apply (eventualGraph_eval _ _).mpr
    refine ⟨x + 1, ?_⟩
    simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
      (ConcreteWitnessGraphs.identity_computation (x + 1) x (lt_add_one x))
  constructor
  · intro hy
    exact eventualGraph_output_unique Kleene.identityIndex x y x hy hi
  · rintro rfl
    exact hi

/-- Minimization of successor supplies an explicitly encoded nowhere-defined
program, whose empty graph equation is provable in PA. -/
theorem eventualGraph_empty :
    Uniform 𝐏𝐀 (eventualGraph ConcreteEmptyGraph.concreteEmptyIndex) empty :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp only [models_iff, uniformSentence_eval, empty_eval, eventualGraph_eval,
    numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ConcreteEmptyGraph.concreteEmpty_unbounded_computation_iff

end

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
