/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GraphQuotient
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.Second
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.Definability

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Graph witnesses for the second-incompleteness obstruction.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

namespace FailureOfComposition

theorem proofBot_consistency_bridge (T : ArithmeticTheory) [T.Δ₁] :
    𝐏𝐀 ⊢ (“(∀ p, ¬!(ProofSearch.proofTarget T ⊥).sigma p) ↔ !T.consistent.val”) :=
  by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  simp [models_iff, Theory.consistent, Bootstrapping.Provable]

theorem numeral_nonproof_of_consistency (T : ArithmeticTheory) [T.Δ₁] [Consistent T] (n : ℕ) :
    𝐏𝐀 ⊢ (ProofSearch.notProofTarget T ⊥).val/[n] :=
  ProofSearch.numeral_negative T ⊥
    (consistent_iff_unprovable_bot.mp (inferInstance : Consistent T)) n

/-- The second-incompleteness route to noncongruence for functional graphs. -/
theorem graph_noncongruence_via_godel (T : ArithmeticTheory) [T.Δ₁] [Consistent T] [𝐏𝐀 ≼ T] :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧
        ProofSearch.Functional I ∧
          ProofSearch.Functional G ∧
            ProofSearch.Pointwise T F I ∧
              ¬ProofSearch.Pointwise T (ProofSearch.comp F G) (ProofSearch.comp I G) :=
  by
  let : 𝐈Σ₁ ≼ T := WeakerThan.trans (𝓣 := 𝐏𝐀) inferInstance inferInstance
  apply ProofSearch.functional_graph_noncongruence T ⊥ T
  · exact consistent_iff_unprovable_bot.mp (inferInstance : Consistent T)
  · simpa [Theory.consistent] using consistent_unprovable T

theorem pa_graph_noncongruence_via_godel :
    ∃ F I G : ProofSearch.Graph,
      ProofSearch.Functional F ∧
        ProofSearch.Functional I ∧
          ProofSearch.Functional G ∧
            ProofSearch.Pointwise 𝐏𝐀 F I ∧
              ¬ProofSearch.Pointwise 𝐏𝐀 (ProofSearch.comp F G) (ProofSearch.comp I G) :=
  graph_noncongruence_via_godel 𝐏𝐀

theorem no_graph_quotient_composition_via_godel (T : ArithmeticTheory) [T.Δ₁] [Consistent T]
    [𝐏𝐀 ≼ T] : ProofSearch.NoQuotientComposition T :=
  ProofSearch.no_quotient_composition_of_graph_noncongruence T (graph_noncongruence_via_godel T)

end FailureOfComposition

end

end PointwiseComposition
