/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GraphQuotient
public import LeanPool.PointwiseComposition.FailureOfComposition.ProductiveDivergence
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.Definability

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Productiveness supplies a true unprovable divergence sentence. Searching for PA
proofs of its halting counterpart gives a Delta-one witness predicate. Internal
Sigma-one completeness connects absence of those proofs to divergence.
This proof does not invoke the second incompleteness theorem.
The proof-search witnesses are a variant of v36's direct computation search.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

namespace FailureOfComposition

theorem graph_noncongruence_of_unprovable_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hex : ∃ d : ℕ, ¬diagonalHalts d ∧ T ⊬ ∼diagonalHaltingFormula/[d]) :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧
        ProofSearch.Functional I ∧
          ProofSearch.Functional G ∧
            ProofSearch.Pointwise T F I ∧
              ¬ProofSearch.Pointwise T (ProofSearch.comp F G) (ProofSearch.comp I G) :=
  by
  let : 𝐈Σ₁ ≼ T := WeakerThan.trans (𝓣 := 𝐏𝐀) inferInstance inferInstance
  obtain ⟨d, hdiv, hnot⟩ := hex
  let σ : ArithmeticSentence := diagonalHaltingFormula/[d]
  have hσ : Hierarchy Σ 1 σ := by simp [σ, diagonalHaltingFormula_sigma]
  have hPA : 𝐏𝐀 ⊬ σ := by
    intro hp
    have hnat : ℕ↓[ℒₒᵣ] ⊧ σ := consequence_iff.mp (Theory.Proof.sound hp) ℕ inferInstance
    apply hdiv
    apply (diagonalHaltingFormula_nat d).mp
    simpa [σ, models_iff, Semiformula.eval_substs, Matrix.constant_eq_singleton] using hnat
  have hAbs : T ⊬ ∼provabilityPred 𝐏𝐀 σ := by
    intro hp
    apply hnot
    have hs : T ⊢ σ ⇒ₗ provabilityPred 𝐏𝐀 σ :=
      WeakerThan.pbl (provable_sigma_one_complete (T := 𝐏𝐀) hσ)
    change T ⊢ ∼σ
    cl_prover[hs, hp]
  exact ProofSearch.functional_graph_noncongruence 𝐏𝐀 σ T hPA hAbs

theorem graph_noncongruence_via_productiveness (T : ArithmeticTheory) [T.Δ₁] [Consistent T]
    [𝐏𝐀 ≼ T] :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧
        ProofSearch.Functional I ∧
          ProofSearch.Functional G ∧
            ProofSearch.Pointwise T F I ∧
              ¬ProofSearch.Pointwise T (ProofSearch.comp F G) (ProofSearch.comp I G) :=
  by exact graph_noncongruence_of_unprovable_divergence T (exists_true_unprovable_divergence T)

theorem pa_graph_noncongruence_via_productiveness :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧
        ProofSearch.Functional I ∧
          ProofSearch.Functional G ∧
            ProofSearch.Pointwise 𝐏𝐀 F I ∧
              ¬ProofSearch.Pointwise 𝐏𝐀 (ProofSearch.comp F G) (ProofSearch.comp I G) :=
  graph_noncongruence_via_productiveness 𝐏𝐀

theorem no_graph_quotient_composition_via_productiveness (T : ArithmeticTheory) [T.Δ₁]
    [Consistent T] [𝐏𝐀 ≼ T] : ProofSearch.NoQuotientComposition T :=
  ProofSearch.no_quotient_composition_of_graph_noncongruence T
    (graph_noncongruence_via_productiveness T)

/-- R.e. is stated directly for the complete theorem-code set. This theorem
has no Delta-one presentation or soundness assumption on T. -/
theorem no_graph_quotient_composition_of_re_theorem_codes (T : ArithmeticTheory) [Consistent T]
    [𝐏𝐀 ≼ T] (hT : REPred (TheoremCodes T)) : ProofSearch.NoQuotientComposition T :=
  ProofSearch.no_quotient_composition_of_graph_noncongruence T
    (graph_noncongruence_of_unprovable_divergence T
      (exists_true_unprovable_divergence_of_theorem_codes T hT))

end FailureOfComposition

end

end PointwiseComposition
