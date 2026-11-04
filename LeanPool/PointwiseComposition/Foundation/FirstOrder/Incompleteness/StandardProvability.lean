/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D2
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D3
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Derivability conditions of standard provability predicate
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic

open ISigma1 Bootstrapping ProvabilityAbstraction

noncomputable instance : Diagonalization 𝐈Σ₁
    where
  fixedpoint := fixedpoint
  diag θ := diagonal θ

section

variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]

local prefix:90 "□" => provabilityPred T

/-- The derivability condition D1. -/
theorem provable_D1 {σ} : T ⊢ σ → 𝐈Σ₁ ⊢ □σ := fun h ↦
  complete 𝐈Σ₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using internalize_provability (V := V) h

/-- The derivability condition D2. -/
theorem provable_D2 {σ π} : 𝐈Σ₁ ⊢ □(σ ⇒ₗ π) ⇒ₗ □σ ⇒ₗ □π :=
  complete 𝐈Σ₁ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T

variable (T)

/-- The standard Provability construction in `FFL.FirstOrder.Theory`. -/
noncomputable abbrev _root_.PointwiseComposition.FFL.FirstOrder.Theory.standardProvability :
    Provability 𝐈Σ₁ T where
  prov := provable T
  bew_def := provable_D1

variable {T}

instance : T.standardProvability.HBL2 :=
  ⟨provable_D2⟩

lemma standardProvability_def (σ : Sentence L) :
    T.standardProvability σ = provabilityPred T σ :=
  rfl

instance : T.standardProvability.SoundOn ℕ :=
  ⟨fun h ↦ by simpa [Arithmetic.standardProvability_def, models_iff] using h⟩

end

section arithmetic

variable {T U : ArithmeticTheory} [T.Δ₁]

local prefix:90 "□" => provabilityPred T

lemma provable_sigma_one_complete [𝐏𝐀⁻ ≼ T] {σ : ArithmeticSentence} (hσ : Hierarchy Σ 1 σ) :
    𝐈Σ₁ ⊢ σ ⇒ₗ □σ :=
  complete 𝐈Σ₁ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using
      Bootstrapping.ObjectArithmetic.sigma_one_complete (T := T) (V := V) hσ

/-- The derivability condition D3. -/
theorem provable_D3 [𝐏𝐀⁻ ≼ T] {σ : ArithmeticSentence} : 𝐈Σ₁ ⊢ □σ ⇒ₗ □□σ :=
  provable_sigma_one_complete (by simp)

open FFL.Entailment FFL.Entailment.FiniteContext

lemma provable_D2_context [𝐈Σ₁ ≼ U] {Γ σ π} (hσπ : Γ ⊢[U] □(σ ⇒ₗ π)) (hσ : Γ ⊢[U] □σ) :
    Γ ⊢[U] □π :=
  FiniteContext.of' (weakening inferInstance provable_D2)⨀hσπ⨀hσ

lemma provable_D3_context [𝐏𝐀⁻ ≼ T] [𝐈Σ₁ ≼ U] {Γ σ} (hσπ : Γ ⊢[U] □σ) : Γ ⊢[U] □□σ :=
  FiniteContext.of' (weakening inferInstance provable_D3)⨀hσπ

lemma provable_sound [U.SoundOnHierarchy Σ 1] {σ} : U ⊢ □σ → T ⊢ σ := fun h ↦
  by
  have : ℕ↓[ℒₒᵣ] ⊧ provabilityPred T σ :=
    ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy Σ 1) h (by simp)
  simpa [models_iff] using this

lemma provable_complete [U.SoundOnHierarchy Σ 1] [𝐈Σ₁ ≼ U] {σ} : T ⊢ σ ↔ U ⊢ □σ :=
  ⟨fun h ↦ weakening inferInstance (provable_D1 h), provable_sound⟩

instance [𝐏𝐀⁻ ≼ T] : T.standardProvability.HBL3 :=
  ⟨provable_D3⟩

instance [𝐏𝐀⁻ ≼ T] : T.standardProvability.HBL where

instance [T.SoundOnHierarchy Σ 1] : T.standardProvability.Kreisel :=
  ⟨fun h ↦ provable_sound h⟩

open FFL.Entailment in
/-- If `π` is equivalent to some Σ₁ sentence `σ`,
  then `π ⇒ₗ □π` is provable in `T` (note: not `𝐈Σ₁`, compare `provable_sigma_one_complete`)
-/
lemma provable_sigma_one_complete_of_E {σ π} [𝐈Σ₁ ≼ T] (hσ : Hierarchy Σ 1 σ)
    (hσπ : 𝐈Σ₁ ⊢ σ ⇔ₗ π) : 𝐈Σ₁ ⊢ π ⇒ₗ □π :=
  by
  apply C_replace ?_ ?_ <| provable_sigma_one_complete (T := T) <| hσ; · cl_prover[hσπ];
  · apply T.standardProvability.mono'; cl_prover[hσπ];

end arithmetic

open FFL.Entailment in
lemma exists_true_but_unprovable_sentence_of_incomplete {T : ArithmeticTheory}
    (h : Incomplete T) : ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  by
  obtain ⟨δ, hδ⟩ := incomplete_def.mp h; by_cases ℕ↓[ℒₒᵣ] ⊧ δ
  · exact ⟨δ, by assumption, hδ.1⟩
  · exact ⟨∼δ, by simpa, hδ.2⟩

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
