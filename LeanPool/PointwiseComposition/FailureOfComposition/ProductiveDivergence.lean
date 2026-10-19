/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Meta.ClProver
public import LeanPool.PointwiseComposition.FailureOfComposition.Productiveness
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The productiveness proof of a true unprovable divergence sentence.
This module does not import or invoke second incompleteness.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

open Encodable Denumerable _root_.Nat.Partrec

namespace FailureOfComposition

noncomputable section

theorem diagonalHalts_re : REPred diagonalHalts := by
  exact (Code.eval_part.comp (Computable.ofNat Code) Computable.id).dom_re

/-- The diagonal Halting Formula construction in `FailureOfComposition`. -/
def diagonalHaltingFormula : ArithmeticSemisentence 1 :=
  codeOfREPred diagonalHalts

theorem diagonalHaltingFormula_sigma : Hierarchy Σ 1 diagonalHaltingFormula := by
  simp [diagonalHaltingFormula, codeOfREPred, codeOfPartrec']

theorem diagonalHaltingFormula_nat (n : ℕ) :
    diagonalHaltingFormula.Evalb ![n] ↔ diagonalHalts n :=
  codeOfREPred_spec diagonalHalts_re

/-- The provable Divergence construction in `FailureOfComposition`. -/
def provableDivergence (T : ArithmeticTheory) (n : ℕ) : Prop :=
  T ⊢ ∼diagonalHaltingFormula/[n]

/-- The numerical set of all theorem codes, using Foundation's sentence coding. -/
def TheoremCodes (T : ArithmeticTheory) (n : ℕ) : Prop :=
  ∃ σ : ArithmeticSentence, (⌜σ⌝ : ℕ) = n ∧ T ⊢ σ

/-- Enumerability of the theorem-code set suffices; no Delta-one presentation
of T is used in this theorem. -/
theorem provableDivergence_re_of_theorem_codes (T : ArithmeticTheory)
    (hT : REPred (TheoremCodes T)) : REPred (provableDivergence T) :=
  by
  let code : ℕ → ℕ := fun n =>
    neg ℒₒᵣ (subst ℒₒᵣ ?[Bootstrapping.ObjectArithmetic.numeral n] ⌜diagonalHaltingFormula⌝)
  have hcode : Computable code :=
    computable_iff_sigma1.mpr
      (by
        dsimp [code]
        definability)
  apply REPred.of_eq (hT.comp hcode)
  intro n
  have heq : code n = (⌜(∼diagonalHaltingFormula/[n] : ArithmeticSentence)⌝ : ℕ) := by
    simp [code, Sentence.quote_def, Semiformula.quote_def, Rewriting.emb_subst_eq_subst_coe₁]
  simp [TheoremCodes, heq, provableDivergence]

theorem provableDivergence_re (T : ArithmeticTheory) [T.Δ₁] : REPred (provableDivergence T) :=
  by
  have h :
    Σ₁-Predicate fun n : ℕ =>
      Bootstrapping.Provable T
        (neg ℒₒᵣ
          (subst ℒₒᵣ ?[Bootstrapping.ObjectArithmetic.numeral n] ⌜diagonalHaltingFormula⌝)) :=
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

/-- Consistency suffices; Sigma-one soundness is not assumed. -/
theorem provableDivergence_sound (T : ArithmeticTheory) [𝐑₀ ≼ T] [Consistent T] (n : ℕ) :
    provableDivergence T n → ¬diagonalHalts n :=
  by
  intro hn hhalt
  have hp : T ⊢ diagonalHaltingFormula/[n] :=
    by
    apply sigma_one_completeness (by simp [diagonalHaltingFormula_sigma])
    simpa [models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using
      (diagonalHaltingFormula_nat n).mpr hhalt
  apply Consistent.not_bot (𝓢 := T)
  have hn : T ⊢ ∼diagonalHaltingFormula/[n] := hn
  cl_prover[hp, hn]

/-- A concrete diagonal computation diverges, but its represented divergence
is not provable in the consistent Delta-one-presented theory. -/
theorem exists_true_unprovable_divergence (T : ArithmeticTheory) [T.Δ₁] [𝐑₀ ≼ T]
    [Consistent T] : ∃ d : ℕ, ¬diagonalHalts d ∧ T ⊬ ∼diagonalHaltingFormula/[d] := by
  exact productive_escape_re (provableDivergence_re T) (provableDivergence_sound T)

theorem exists_true_unprovable_divergence_of_theorem_codes (T : ArithmeticTheory) [𝐑₀ ≼ T]
    [Consistent T] (hT : REPred (TheoremCodes T)) :
    ∃ d : ℕ, ¬diagonalHalts d ∧ T ⊬ ∼diagonalHaltingFormula/[d] := by
  exact
    productive_escape_re (provableDivergence_re_of_theorem_codes T hT)
      (provableDivergence_sound T)

end

end FailureOfComposition

end

end PointwiseComposition
