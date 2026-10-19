/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneDefinitions
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.Definability

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Right compatibility forces every true Pi-one sentence to be provable. The
witnesses search for PA proofs of the negation of the proposed sentence.
Only PA standard soundness is used; no soundness or consistency of T is assumed.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping FFL.Entailment

namespace FailureOfComposition
namespace PiOneCharacterization

/-- A true Pi-one sentence omitted by T gives functional graphs witnessing
failure of right compatibility. -/
theorem graph_noncongruence_of_true_unprovable_pi_one (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (σ : ArithmeticSentence) (hσ : Hierarchy Π 1 σ) (htrue : ℕ↓[ℒₒᵣ] ⊧ σ) (hnot : T ⊬ σ) :
    ∃ F H G : ProofSearch.Graph,
      ProofSearch.Functional F ∧
        ProofSearch.Functional H ∧
          ProofSearch.Functional G ∧
            ProofSearch.Pointwise T F H ∧
              ¬ProofSearch.Pointwise T (ProofSearch.comp F G) (ProofSearch.comp H G) :=
  by
  let : 𝐈Σ₁ ≼ T := WeakerThan.trans (𝓣 := 𝐏𝐀) inferInstance inferInstance
  have hneg : Hierarchy Σ 1 (∼σ) := by simpa using hσ
  have hPA : 𝐏𝐀 ⊬ ∼σ := by
    intro hp
    have hn : ℕ↓[ℒₒᵣ] ⊧ ∼σ := consequence_iff.mp (Theory.Proof.sound hp) ℕ inferInstance
    have hfalse : ¬ℕ↓[ℒₒᵣ] ⊧ σ := by simpa [models_iff] using hn
    exact hfalse htrue
  have hAbs : T ⊬ ∼provabilityPred 𝐏𝐀 (∼σ) :=
    by
    intro hp
    apply hnot
    have hs : T ⊢ ∼σ ⇒ₗ provabilityPred 𝐏𝐀 (∼σ) :=
      WeakerThan.pbl (provable_sigma_one_complete (T := 𝐏𝐀) hneg)
    cl_prover[hs, hp]
  exact ProofSearch.functional_graph_noncongruence 𝐏𝐀 (∼σ) T hPA hAbs

/-- No consistency or effective presentation of T is needed for necessity. -/
theorem rightCompatible_implies_piOneComplete (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h : RightCompatible T) : PiOneComplete T :=
  by
  intro σ hσ htrue
  by_contra hnot
  obtain ⟨F, H, G, hF, hH, hG, hFH, hcomp⟩ :=
    graph_noncongruence_of_true_unprovable_pi_one T σ hσ htrue hnot
  exact hcomp (h F H G hF hH hG hFH)

end PiOneCharacterization
end FailureOfComposition

end

end PointwiseComposition
