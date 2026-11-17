/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneDefinitions

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Pi-one completeness identifies external pointwise provability with equality
of functional Sigma-one graphs on the natural numbers. No enumerability
assumption is used.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace PiOneCharacterization

open ProofSearch

/-- A closed convergence assertion with both arguments standard numerals. -/
def graphInstance (F : Graph) (n m : ℕ) : ArithmeticSentence :=
  “!F.val !!(n)!!(m)”

/-- Absence of an output at one fixed standard input. -/
def divergesAt (F : Graph) (n : ℕ) : ArithmeticSentence :=
  “∀ y, ¬!F.val !!(n)y”

theorem graphInstance_sigma_one (F : Graph) (n m : ℕ) : Hierarchy Σ 1 (graphInstance F n m) :=
  by simp [graphInstance]

theorem divergesAt_pi_one (F : Graph) (n : ℕ) : Hierarchy Π 1 (divergesAt F n) := by
  simp [divergesAt]

section Semantics

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

@[simp]
theorem graphInstance_eval (F : Graph) (n m : ℕ) :
    (graphInstance F n m).Evalb (M := M) ![] ↔ F.val.Evalb ![(n : M), (m : M)] := by
  simp [graphInstance, numeral_eq_natCast]

@[simp]
theorem divergesAt_eval (F : Graph) (n : ℕ) :
    (divergesAt F n).Evalb (M := M) ![] ↔ ∀ y : M, ¬F.val.Evalb ![(n : M), y] := by
  simp [divergesAt, numeral_eq_natCast]

end Semantics

/-- A consistent Pi-one-complete theory cannot prove a false Sigma-one
sentence: it already proves that sentence's true Pi-one negation. -/
theorem sigma_one_sound_of_pi_one_complete (T : ArithmeticTheory) [Consistent T]
    (hT : PiOneComplete T) (σ : ArithmeticSentence) (hσ : Hierarchy Σ 1 σ) (hp : T ⊢ σ) :
    ℕ↓[ℒₒᵣ] ⊧ σ := by
  by_contra hn
  have hnσ : T ⊢ ∼σ := hT (∼σ) (by simpa using hσ.neg) (by simpa using hn)
  apply Consistent.not_bot (𝓢 := T)
  cl_prover[hp, hnσ]

/-- True ground convergence assertions are provable already in PA. -/
theorem true_graph_instance_provable (F : Graph) (n m : ℕ) (h : F.val.Evalb ![n, m]) :
    𝐏𝐀 ⊢ graphInstance F n m :=
  by
  apply sigma_one_completeness (graphInstance_sigma_one F n m)
  simpa only [models_iff, graphInstance_eval, natCast_nat] using h

/-- Pointwise provability transports a true ground graph instance to a proof in the theory. -/
theorem ground_proof_of_pointwise (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (F G : Graph)
    (hFG : Pointwise T F G) (n m : ℕ) (hF : F.val.Evalb ![n, m]) : T ⊢ graphInstance G n m :=
  by
  have hpF : T ⊢ graphInstance F n m := WeakerThan.pbl (true_graph_instance_provable F n m hF)
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀 := models_of_subtheory (U := T) inferInstance
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hEq : M↓[ℒₒᵣ] ⊧ eqAt F G n :=
    consequence_iff.mp (Theory.Proof.sound (hFG n)) M inferInstance
  have hVal : M↓[ℒₒᵣ] ⊧ graphInstance F n m :=
    consequence_iff.mp (Theory.Proof.sound hpF) M inferInstance
  simp only [models_iff, eqAt_eval] at hEq
  simp only [models_iff, graphInstance_eval] at hVal ⊢
  exact (hEq (m : M)).mp hVal

/-- Pi-one completeness and consistency make pointwise provability sound for
the represented graphs, including their individual convergence assertions. -/
theorem pointwise_implies_extensional (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : PiOneComplete T) (F G : Graph) (hFG : Pointwise T F G) : Extensional F G :=
  by
  intro n m
  have forward {F G : Graph} (hFG : Pointwise T F G) (hF : F.val.Evalb ![n, m]) :
    G.val.Evalb ![n, m] :=
    by
    have hp := ground_proof_of_pointwise T F G hFG n m hF
    have hs := sigma_one_sound_of_pi_one_complete T hT _ (graphInstance_sigma_one G n m) hp
    simpa only [models_iff, graphInstance_eval, natCast_nat] using hs
  exact ⟨forward hFG, forward ((pointwise_equivalence T).symm hFG)⟩

private theorem eqAt_provable_of_common_value (F G : Graph) (hF : Functional F)
    (hG : Functional G) (n m : ℕ) (hnF : F.val.Evalb ![n, m]) (hnG : G.val.Evalb ![n, m]) :
    𝐏𝐀 ⊢ eqAt F G n :=
  by
  have hpF := true_graph_instance_provable F n m hnF
  have hpG := true_graph_instance_provable G n m hnG
  apply complete.{0} 𝐏𝐀
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hf : M↓[ℒₒᵣ] ⊧ functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) M inferInstance
  have hg : M↓[ℒₒᵣ] ⊧ functionalSentence G :=
    consequence_iff.mp (Theory.Proof.sound hG) M inferInstance
  have hvF : M↓[ℒₒᵣ] ⊧ graphInstance F n m :=
    consequence_iff.mp (Theory.Proof.sound hpF) M inferInstance
  have hvG : M↓[ℒₒᵣ] ⊧ graphInstance G n m :=
    consequence_iff.mp (Theory.Proof.sound hpG) M inferInstance
  simp only [models_iff, functionalSentence_eval] at hf hg
  simp only [models_iff, graphInstance_eval] at hvF hvG
  rw [models_iff, eqAt_eval]
  intro y
  constructor
  · intro hy
    simpa only [hf (n : M) y (m : M) hy hvF] using hvG
  · intro hy
    simpa only [hg (n : M) y (m : M) hy hvG] using hvF

private theorem eqAt_provable_of_divergence (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : PiOneComplete T) (F G : Graph) (n : ℕ) (hF : ∀ m : ℕ, ¬F.val.Evalb ![n, m])
    (hG : ∀ m : ℕ, ¬G.val.Evalb ![n, m]) : T ⊢ eqAt F G n :=
  by
  have hdF : T ⊢ divergesAt F n :=
    hT _ (divergesAt_pi_one F n)
      (by simpa only [models_iff, divergesAt_eval, natCast_nat] using hF)
  have hdG : T ⊢ divergesAt G n :=
    hT _ (divergesAt_pi_one G n)
      (by simpa only [models_iff, divergesAt_eval, natCast_nat] using hG)
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀 := models_of_subtheory (U := T) inferInstance
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hf : M↓[ℒₒᵣ] ⊧ divergesAt F n :=
    consequence_iff.mp (Theory.Proof.sound hdF) M inferInstance
  have hg : M↓[ℒₒᵣ] ⊧ divergesAt G n :=
    consequence_iff.mp (Theory.Proof.sound hdG) M inferInstance
  simp only [models_iff, divergesAt_eval] at hf hg
  rw [models_iff, eqAt_eval]
  intro y
  exact iff_of_false (hf y) (hg y)

/-- Equality of functional standard graphs gives pointwise provability:
common values use PA computation proofs; joint divergence uses Pi-one
completeness. This direction does not require consistency. -/
theorem extensional_implies_pointwise (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (hT : PiOneComplete T)
    (F G : Graph) (hF : Functional F) (hG : Functional G) (hFG : Extensional F G) :
    Pointwise T F G := by
  intro n
  classical
  by_cases hconv : ∃ m : ℕ, F.val.Evalb ![n, m]
  · obtain ⟨m, hm⟩ := hconv
    exact WeakerThan.pbl (eqAt_provable_of_common_value F G hF hG n m hm ((hFG n m).mp hm))
  · have hnF : ∀ m : ℕ, ¬F.val.Evalb ![n, m] := fun m hm => hconv ⟨m, hm⟩
    have hnG : ∀ m : ℕ, ¬G.val.Evalb ![n, m] := fun m hm => hnF m ((hFG n m).mpr hm)
    exact eqAt_provable_of_divergence T hT F G n hnF hnG

theorem pointwise_iff_extensional (T : ArithmeticTheory) [𝐏𝐀 ≼ T] [Consistent T]
    (hT : PiOneComplete T) (F G : Graph) (hF : Functional F) (hG : Functional G) :
    Pointwise T F G ↔ Extensional F G :=
  ⟨pointwise_implies_extensional T hT F G, extensional_implies_pointwise T hT F G hF hG⟩

theorem piOneComplete_implies_agreesWithExtensional (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    [Consistent T] (hT : PiOneComplete T) : AgreesWithExtensional T := fun F G hF hG =>
  pointwise_iff_extensional T hT F G hF hG

end PiOneCharacterization
end FailureOfComposition

end

end PointwiseComposition
