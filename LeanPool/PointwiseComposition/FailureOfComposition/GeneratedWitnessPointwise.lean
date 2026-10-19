/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneExtensionality
public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedWitnessGraphs

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The stage-restricted witnesses are pointwise PA-equivalent whenever the
underlying graphs agree on the standard naturals. A true ground equation for
the total history evaluator fixes all possible internal outputs at that
standard stage and input. No uniform equivalence premise is assumed.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition
namespace GeneratedWitnessGraphs

open ProofSearch ConcreteEvaluator PiOneCharacterization

private theorem history_output_at_numerals (e s x z : ℕ)
    (hz : Semiformula.Evalb ![z, s, e, x] (code codeHistoryEvaluator)) {M : Type*}
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] :
    Semiformula.Evalb ![(z : M), (s : M), (e : M), (x : M)] (code codeHistoryEvaluator) :=
  by
  have htr :=
    FFL.FirstOrder.Arithmetic.bold_sigma_one_completeness' (M := M)
      (code_sigma_one codeHistoryEvaluator) hz
  rw [numeral_eq_natCast] at htr
  have heq : (Nat.cast ∘ ![z, s, e, x] : Fin 4 → M) = ![(z : M), (s : M), (e : M), (x : M)] :=
    by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i1
      refine Fin.cases ?_ ?_ i1
      · rfl
      · intro i2
        refine Fin.cases ?_ ?_ i2
        · rfl
        · intro i3
          refine Fin.cases ?_ (fun i4 => Fin.elim0 i4) i3
          rfl
  rw [heq] at htr
  exact htr

/-- A fixed standard stage can only return its genuine standard output in
any PA model. Standard agreement then supplies the second graph at that output. -/
private theorem standard_stage_implies_graph (e : ℕ) (G : Graph)
    (hExt : Extensional (eventualGraph e) G) (s x : ℕ) {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧] (y : M)
    (hy :
      Semiformula.Evalb ![(s : M), (e : M), (x : M), y]
        (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    G.val.Evalb ![(x : M), y] :=
  by
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  obtain ⟨z, hz⟩ := eval_codeHistoryEvaluator_exists (s : ℕ) e x
  have hzM := history_output_at_numerals e s x z hz (M := M)
  have hyz := eval_unique ((evalnCertificateFormula_eval_history_iff _ _ _ _).mp hy) hzM
  cases z with
  | zero =>
    have heq : y + 1 = 0 := by simpa only [Nat.cast_zero] using hyz
    exact False.elim ((ne_of_gt (lt_of_le_of_lt (Arithmetic.zero_le y) (lt_add_one y))) heq)
  | succ m =>
    have heq : y = (m : M) := by simpa using hyz
    have hm :
      Semiformula.Evalb ![s, e, x, m] (evalnCertificateFormula : ArithmeticSemisentence 4) :=
      (evalnCertificateFormula_eval_history_iff s e x m).mpr (by simpa using hz)
    have hE : (eventualGraph e).val.Evalb ![x, m] :=
      by
      apply (eventualGraph_eval e _).mpr
      refine ⟨s, ?_⟩
      simpa only [numeral_eq_natCast_app, natCast_nat, Matrix.cons_val_zero,
        Matrix.cons_val_one] using hm
    have hG := true_graph_instance_provable G x m ((hExt x m).mp hE)
    have hv := consequence_iff.mp (Theory.Proof.sound hG) M inferInstance
    have hval : G.val.Evalb ![(x : M), (m : M)] := by
      simpa only [models_iff, graphInstance_eval] using hv
    simpa only [heq] using hval

/-- At each fixed standard stage/input pair, PA proves equality of the two
witness graphs over all internal outputs. -/
theorem AGraph_eqAt_B_pair (e : ℕ) (G : Graph) (hExt : Extensional (eventualGraph e) G)
    (s x : ℕ) : 𝐏𝐀 ⊢ eqAt (AGraph e G) (BGraph e) (Nat.pair s x) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  rw [models_iff, eqAt_eval]
  intro y
  rw [coe_pair_eq_pair_coe, AGraph_pair_eval, BGraph_pair_eval]
  constructor
  · exact And.left
  · intro h
    exact
      ⟨h,
        standard_stage_implies_graph e G hExt s x y
          ((stageGraph_eval e (s : M) (x : M) y).mp h)⟩

/-- Standard equality of the original graphs suffices for pointwise
PA-provable equality of the stage-restricted witnesses. No functionality
assumption on G and no uniform-equivalence premise is needed. -/
theorem AGraph_pointwise_B (e : ℕ) (G : Graph) (hExt : Extensional (eventualGraph e) G) :
    Pointwise 𝐏𝐀 (AGraph e G) (BGraph e) := by
  intro n
  simpa only [Nat.pair_unpair] using
    AGraph_eqAt_B_pair e G hExt (Nat.unpair n).1 (Nat.unpair n).2

end GeneratedWitnessGraphs
end FailureOfComposition

end

end PointwiseComposition
