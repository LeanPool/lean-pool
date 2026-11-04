/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.ProofSearchTemplate
public import LeanPool.PointwiseComposition.FailureOfComposition.QuotientObstruction

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
Pointwise graph equality and quotient operations.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace ProofSearch

noncomputable section

theorem pointwise_equivalence (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Equivalence (Pointwise T)
    where
  refl F
    n := by
    apply WeakerThan.pbl (𝓢 := 𝐏𝐀)
    apply complete.{0} 𝐏𝐀
    intro V _ _
    have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
    simp [models_iff, eqAt]
  symm := by
    intro F G h n
    have hs : 𝐏𝐀 ⊢ eqAt F G n ⇒ₗ eqAt G F n :=
      by
      apply complete.{0} 𝐏𝐀
      intro V _ _
      have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
      simp only [Semantics.Imp.models_imply, models_iff, eqAt_eval, Nat.succ_eq_add_one,
        Nat.reduceAdd]
      intro h y
      exact (h y).symm
    exact Entailment.mdp (WeakerThan.pbl hs) (h n)
  trans := by
    intro F G H hFG hGH n
    have ht : 𝐏𝐀 ⊢ eqAt F G n ⇒ₗ eqAt G H n ⇒ₗ eqAt F H n :=
      by
      apply complete.{0} 𝐏𝐀
      intro V _ _
      have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
      simp only [Semantics.Imp.models_imply, models_iff, eqAt_eval, Nat.succ_eq_add_one,
        Nat.reduceAdd]
      intro hfg hgh y
      exact (hfg y).trans (hgh y)
    exact Entailment.mdp (Entailment.mdp (WeakerThan.pbl ht) (hFG n)) (hGH n)

theorem comp_functional {F G : Graph} (hF : Functional F) (hG : Functional G) :
    Functional (comp F G) := by
  apply complete.{0} 𝐏𝐀
  intro V _ _
  have : V↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hf : V↓[ℒₒᵣ] ⊧ functionalSentence F :=
    consequence_iff.mp (Theory.Proof.sound hF) V inferInstance
  have hg : V↓[ℒₒᵣ] ⊧ functionalSentence G :=
    consequence_iff.mp (Theory.Proof.sound hG) V inferInstance
  simp only [models_iff, functionalSentence_eval, Nat.succ_eq_add_one, Nat.reduceAdd] at hf hg
  simp only [models_iff, functionalSentence_eval, Nat.succ_eq_add_one, Nat.reduceAdd, comp_eval,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.Fin1.eq_one,
    Matrix.cons_val_fin_one, forall_exists_index, and_imp]
  intro x y z a hga hfay b hgb hfbz
  have hab := hg x a b hga hgb
  subst b
  exact hf a y z hfay hfbz

/-- The Functional Graph construction in `FailureOfComposition.ProofSearch`. -/
def FunctionalGraph :=
  { F : Graph // Functional F }

/-- The functional Comp construction in `FailureOfComposition.ProofSearch`. -/
def functionalComp (F G : FunctionalGraph) : FunctionalGraph :=
  ⟨comp F.val G.val, comp_functional F.property G.property⟩

/-- The pointwise Setoid construction in `FailureOfComposition.ProofSearch`. -/
def pointwiseSetoid (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Setoid FunctionalGraph
    where
  r F G := Pointwise T F.val G.val
  iseqv :=
    { refl := fun F => (pointwise_equivalence T).refl F.val
      symm := fun h => (pointwise_equivalence T).symm h
      trans := fun h₁ h₂ => (pointwise_equivalence T).trans h₁ h₂ }

/-- The No Quotient Composition construction in `FailureOfComposition.ProofSearch`. -/
def NoQuotientComposition (T : ArithmeticTheory) [𝐏𝐀 ≼ T] : Prop :=
  ¬∃ C :
      Quotient (pointwiseSetoid T) →
        Quotient (pointwiseSetoid T) → Quotient (pointwiseSetoid T),
      ∀ F G,
        C (Quotient.mk (pointwiseSetoid T) F) (Quotient.mk (pointwiseSetoid T) G) =
          Quotient.mk (pointwiseSetoid T) (functionalComp F G)

theorem no_quotient_composition_of_graph_noncongruence (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h :
      ∃ F I G : Graph,
        Functional F ∧
          Functional I ∧ Functional G ∧ Pointwise T F I ∧ ¬Pointwise T (comp F G) (comp I G)) :
    NoQuotientComposition T :=
  by
  obtain ⟨F, I, G, hF, hI, hG, hFI, hcomp⟩ := h
  exact
    FailureOfComposition.no_quotient_composition_of_noncongruence (pointwiseSetoid T)
      functionalComp ⟨F, hF⟩ ⟨I, hI⟩ ⟨G, hG⟩ hFI hcomp

end

end ProofSearch
end FailureOfComposition

end

end PointwiseComposition
