/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedGraphDefinitions
public import LeanPool.PointwiseComposition.FailureOfComposition.PiOneCongruence
public import LeanPool.PointwiseComposition.FailureOfComposition.GeneratedSoundness

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
The two algebraic halves of the generated-congruence dichotomy. Sigma-one
soundness makes the closure extensionally sound; a false proved Sigma-one
sentence collapses it once extensional containment has been established.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace FailureOfComposition
namespace GeneratedCongruence

open ProofSearch PiOneCharacterization

/-- The delta Graph construction in `FailureOfComposition.GeneratedCongruence`. -/
def deltaGraph (σ : Σ₁.Sentence) : Graph :=
  .mkSigma (“x y. !σ.val ∧ y = x”)

@[simp]
theorem deltaGraph_eval {M : Type*} [ORingStructure M] (σ : Σ₁.Sentence) (v : Fin 2 → M) :
    (deltaGraph σ).val.Evalb v ↔ σ.val.Evalb (M := M) ![] ∧ v 1 = v 0 := by simp [deltaGraph]

theorem deltaGraph_functional (σ : Σ₁.Sentence) : Functional (deltaGraph σ) :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  have hy' := (deltaGraph_eval σ _).mp hy
  have hz' := (deltaGraph_eval σ _).mp hz
  exact hy'.2.trans hz'.2.symm

theorem deltaGraph_pointwise_identity (T : ArithmeticTheory) [𝐏𝐀 ≼ T] (σ : Σ₁.Sentence)
    (hp : T ⊢ σ.val) : Pointwise T (deltaGraph σ) identity :=
  by
  intro n
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝐏𝐀 := models_of_subtheory (U := T) inferInstance
  have : M↓[ℒₒᵣ] ⊧* 𝐈Σ₁ := models_of_subtheory (U := 𝐏𝐀) inferInstance
  have hs : M↓[ℒₒᵣ] ⊧ σ.val := consequence_iff.mp (Theory.Proof.sound hp) M inferInstance
  simp only [models_iff] at hs
  simp [models_iff, eqAt_eval, deltaGraph_eval, hs]

theorem deltaGraph_extensional_empty (σ : Σ₁.Sentence) (hn : ¬ℕ↓[ℒₒᵣ] ⊧ σ.val) :
    Extensional (deltaGraph σ) empty := by
  intro x y
  have hs : ¬σ.val.Evalb (M := ℕ) ![] := by simpa only [models_iff] using hn
  simp [deltaGraph_eval, hs]

theorem comp_right_identity (F : Graph) : Uniform 𝐏𝐀 (comp F identity) F :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  simp [models_iff]

theorem comp_right_empty (F : Graph) : Uniform 𝐏𝐀 (comp F empty) empty :=
  by
  apply complete.{0} 𝐏𝐀
  intro M _ _
  simp [models_iff]

/-- The identity and empty graphs as PA-functional graph objects. -/
def identityGraph : FunctionalGraph :=
  ⟨identity, identity_functional⟩

/-- The empty Graph construction in `FailureOfComposition.GeneratedCongruence`. -/
def emptyGraph : FunctionalGraph :=
  ⟨empty, by
    apply complete.{0} 𝐏𝐀
    intro M _ _
    simp [models_iff]⟩

/-- The delta Functional Graph construction in `FailureOfComposition.GeneratedCongruence`. -/
def deltaFunctionalGraph (σ : Σ₁.Sentence) : FunctionalGraph :=
  ⟨deltaGraph σ, deltaGraph_functional σ⟩

/-- Identifying the identity with the empty graph collapses every program. -/
theorem collapse_of_identity_rel_empty (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (h : Rel T identityGraph emptyGraph) : ∀ F G : FunctionalGraph, Rel T F G :=
  by
  have hzero (F : FunctionalGraph) : Rel T F emptyGraph :=
    by
    have hi : Rel T (functionalComp F identityGraph) F :=
      rel_of_uniform T (comp_right_identity F.val)
    have hz : Rel T (functionalComp F emptyGraph) emptyGraph :=
      rel_of_uniform T (comp_right_empty F.val)
    exact rel_trans T (rel_symm T hi) (rel_trans T (rel_comp T (rel_refl T F) h) hz)
  intro F G
  exact rel_trans T (hzero F) (rel_symm T (hzero G))

/-- A false proved Sigma-one sentence identifies the identity and empty graphs
once standard extensional equality is contained in the generated relation. -/
theorem identity_rel_empty_of_false_proved_sigma_one (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hExt : ∀ F G : FunctionalGraph, Extensional F.val G.val → Rel T F G) (σ : Σ₁.Sentence)
    (hp : T ⊢ σ.val) (hn : ¬ℕ↓[ℒₒᵣ] ⊧ σ.val) : Rel T identityGraph emptyGraph :=
  by
  have hi : Rel T (deltaFunctionalGraph σ) identityGraph :=
    rel_base T (deltaGraph_pointwise_identity T σ hp)
  have hz : Rel T (deltaFunctionalGraph σ) emptyGraph :=
    hExt _ _ (deltaGraph_extensional_empty σ hn)
  exact rel_trans T (rel_symm T hi) hz

/-- Without Sigma-one soundness the generated relation is universal. The
extensional-containment hypothesis is discharged by the computation witnesses. -/
theorem collapse_of_not_sigmaOneSound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hExt : ∀ F G : FunctionalGraph, Extensional F.val G.val → Rel T F G)
    (hT : ¬SigmaOneSound T) : ∀ F G : FunctionalGraph, Rel T F G :=
  by
  obtain ⟨σ, hσ, hp, hn⟩ := (not_sigmaOneSound_iff T).mp hT
  exact
    collapse_of_identity_rel_empty T
      (identity_rel_empty_of_false_proved_sigma_one T hExt (.mkSigma σ hσ) hp hn)

/-- Sigma-one soundness makes the generated congruence extensionally sound. -/
theorem generated_implies_extensional_of_sigmaOneSound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hT : SigmaOneSound T) {F G : FunctionalGraph} (h : Rel T F G) : Extensional F.val G.val :=
  by
  apply h (fun H K : FunctionalGraph => Extensional H.val K.val)
  · constructor
    · refine ⟨?_, ?_, ?_⟩
      · intro H x y
        exact Iff.rfl
      · intro H K hHK x y
        exact (hHK x y).symm
      · intro H K L hHK hKL x y
        exact (hHK x y).trans (hKL x y)
    · intro H H' K K' hH hK
      exact extensional_comp hH hK
  · intro H K hHK
    exact pointwise_implies_extensional_of_sigmaOneSound T hT H.val K.val hHK

/-- Extensional containment and Sigma-one soundness identify the generated
relation with standard graph equality. -/
theorem rel_iff_extensional_of_sigmaOneSound (T : ArithmeticTheory) [𝐏𝐀 ≼ T]
    (hExt : ∀ F G : FunctionalGraph, Extensional F.val G.val → Rel T F G) (hT : SigmaOneSound T)
    (F G : FunctionalGraph) : Rel T F G ↔ Extensional F.val G.val :=
  ⟨generated_implies_extensional_of_sigmaOneSound T hT, hExt F G⟩

end GeneratedCongruence
end FailureOfComposition

end

end PointwiseComposition
