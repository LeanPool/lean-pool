/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ConcreteAdequacy
public import LeanPool.PointwiseComposition.FailureOfComposition.ProductiveDivergence

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Productiveness for the diagonal halting formula of the actual history
evaluator. The formula is built directly from `evalnCertificateFormula`;
no representation chosen by `codeOfREPred` occurs in its definition.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

namespace FailureOfComposition
namespace ConcreteEvaluator

noncomputable section

/-- The diagonal computation of the actual arithmetized history evaluator. -/
def diagonalHistoryFormula : ArithmeticSemisentence 1 :=
  “q. ∃ s y, !CategoricalRiceShapiro.Evaluator.evalnCertificateFormula.val s q q y”

theorem diagonalHistoryFormula_sigma : Hierarchy Σ 1 diagonalHistoryFormula := by
  simp [diagonalHistoryFormula]

/-- The diagonal formula quantifies over all model stages and outputs. -/
theorem diagonalHistoryFormula_eval_model {M : Type*} [ORingStructure M] (q : M) :
    diagonalHistoryFormula.Evalb ![q] ↔
      ∃ s y : M,
        Semiformula.Evalb ![s, q, q, y]
          (CategoricalRiceShapiro.Evaluator.evalnCertificateFormula :
            ArithmeticSemisentence 4) :=
  by simp [diagonalHistoryFormula]

/-- Specializing the program parameter is the same as its fixed-index graph. -/
theorem diagonalHistoryFormula_eval (n : ℕ) :
    diagonalHistoryFormula.Evalb ![n] ↔ ∃ y : ℕ, (eventualGraph n).val.Evalb ![n, y] :=
  by
  simp only [diagonalHistoryFormula, eventualGraph_eval]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Semiformula.eval_ex,
    Semiformula.eval_substs, Matrix.comp₄, Semiterm.val_bvar, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.cons_app_two, Fin.Fin1.eq_one, Matrix.cons_val_fin_one,
    Nat.numeral_eq]
  constructor
  · rintro ⟨s, y, h⟩
    exact ⟨y, s, h⟩
  · rintro ⟨y, s, h⟩
    exact ⟨s, y, h⟩

/-- The represented divergence sentences provable in T. -/
def provableHistoryDivergence (T : ArithmeticTheory) (n : ℕ) : Prop :=
  T ⊢ ∼diagonalHistoryFormula/[n]

/-- The theorem-code assumption directly enumerates these concrete sentences. -/
theorem provableHistoryDivergence_re_of_theorem_codes (T : ArithmeticTheory)
    (hT : REPred (FailureOfComposition.TheoremCodes T)) :
    REPred (provableHistoryDivergence T) :=
  by
  let code : ℕ → ℕ := fun n =>
    neg ℒₒᵣ (subst ℒₒᵣ ?[Bootstrapping.ObjectArithmetic.numeral n] ⌜diagonalHistoryFormula⌝)
  have hcode : Computable code :=
    computable_iff_sigma1.mpr
      (by
        dsimp [code]
        definability)
  apply REPred.of_eq (hT.comp hcode)
  intro n
  have heq : code n = (⌜(∼diagonalHistoryFormula/[n] : ArithmeticSentence)⌝ : ℕ) := by
    simp [code, Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]
  simp [FailureOfComposition.TheoremCodes, heq, provableHistoryDivergence]

/-- A Delta-one theory presentation also enumerates the concrete sentences. -/
theorem provableHistoryDivergence_re (T : ArithmeticTheory) [T.Δ₁] :
    REPred (provableHistoryDivergence T) :=
  by
  have h :
    Σ₁-Predicate fun n : ℕ =>
      Bootstrapping.Provable T
        (neg ℒₒᵣ
          (subst ℒₒᵣ ?[Bootstrapping.ObjectArithmetic.numeral n] ⌜diagonalHistoryFormula⌝)) :=
    by definability
  apply REPred.of_eq (rePred_iff_sigma1.mpr h)
  intro n
  constructor
  · intro hp
    apply Bootstrapping.Provable.sound
    simpa [Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁] using
      hp
  · intro hp
    simpa [Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁] using
      internalize_provability (V := ℕ) hp

/-- Consistency excludes a proved divergence when this concrete Sigma-one
halting formula is true. No Sigma-one soundness assumption on T is needed. -/
theorem provableHistoryDivergence_sound_eval (T : ArithmeticTheory) [𝐑₀ ≼ T] [Consistent T]
    (n : ℕ) : provableHistoryDivergence T n → ¬diagonalHistoryFormula.Evalb ![n] :=
  by
  intro hn hhalt
  have hp : T ⊢ diagonalHistoryFormula/[n] :=
    by
    apply sigma_one_completeness (by simp [diagonalHistoryFormula_sigma])
    simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using hhalt
  apply Consistent.not_bot (𝓢 := T)
  have hn : T ⊢ ∼diagonalHistoryFormula/[n] := hn
  cl_prover[hp, hn]

/-- Standard-model adequacy for the actual diagonal history formula. -/
theorem diagonalHistoryFormula_nat (n : ℕ) :
    diagonalHistoryFormula.Evalb ![n] ↔ FailureOfComposition.diagonalHalts n :=
  by
  rw [diagonalHistoryFormula_eval]
  simp only [eventualGraph_adequate]
  exact Part.dom_iff_mem.symm

/-- Consistency suffices to make the enumerable provable-divergence set a
subset of the genuinely divergent diagonal computations. -/
theorem provableHistoryDivergence_sound (T : ArithmeticTheory) [𝐑₀ ≼ T] [Consistent T] (n : ℕ) :
    provableHistoryDivergence T n → ¬FailureOfComposition.diagonalHalts n :=
  by
  intro hn hh
  exact provableHistoryDivergence_sound_eval T n hn ((diagonalHistoryFormula_nat n).mpr hh)

/-- Productiveness supplies an unprovable divergence sentence for the actual
program-index history formula, without Gödel's second incompleteness theorem. -/
theorem exists_unprovable_diagonal_history_divergence_of_theorem_codes (T : ArithmeticTheory)
    [𝐑₀ ≼ T] [Consistent T] (hT : REPred (FailureOfComposition.TheoremCodes T)) :
    ∃ d : ℕ, ¬FailureOfComposition.diagonalHalts d ∧ T ⊬ ∼diagonalHistoryFormula/[d] := by
  exact
    FailureOfComposition.productive_escape_re
      (provableHistoryDivergence_re_of_theorem_codes T hT) (provableHistoryDivergence_sound T)

/-- The same result from Foundation's Delta-one theory presentation. -/
theorem exists_unprovable_diagonal_history_divergence (T : ArithmeticTheory) [T.Δ₁] [𝐑₀ ≼ T]
    [Consistent T] :
    ∃ d : ℕ, ¬FailureOfComposition.diagonalHalts d ∧ T ⊬ ∼diagonalHistoryFormula/[d] := by
  exact
    FailureOfComposition.productive_escape_re (provableHistoryDivergence_re T)
      (provableHistoryDivergence_sound T)

/-- The selected divergence is true for the concrete arithmetical formula. -/
theorem exists_true_unprovable_history_divergence_of_theorem_codes (T : ArithmeticTheory)
    [𝐑₀ ≼ T] [Consistent T] (hT : REPred (FailureOfComposition.TheoremCodes T)) :
    ∃ d : ℕ, ¬diagonalHistoryFormula.Evalb ![d] ∧ T ⊬ ∼diagonalHistoryFormula/[d] :=
  by
  obtain ⟨d, hd, hu⟩ := exists_unprovable_diagonal_history_divergence_of_theorem_codes T hT
  exact ⟨d, fun h => hd ((diagonalHistoryFormula_nat d).mp h), hu⟩

/-- Concrete arithmetical divergence under a Delta-one theory presentation. -/
theorem exists_true_unprovable_history_divergence (T : ArithmeticTheory) [T.Δ₁] [𝐑₀ ≼ T]
    [Consistent T] :
    ∃ d : ℕ, ¬diagonalHistoryFormula.Evalb ![d] ∧ T ⊬ ∼diagonalHistoryFormula/[d] :=
  by
  obtain ⟨d, hd, hu⟩ := exists_unprovable_diagonal_history_divergence T
  exact ⟨d, fun h => hd ((diagonalHistoryFormula_nat d).mp h), hu⟩

end

end ConcreteEvaluator
end FailureOfComposition

end

end PointwiseComposition
