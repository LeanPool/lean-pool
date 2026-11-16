/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Thomas Zhu
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
module

public import LeanPool.KLS.BrownianMotion.Auxiliary.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Probability.Martingale.Basic

/-!
# Properties of martingales and submartingales

This file contains auxiliary results about martingales and submartingales that are not yet in
Mathlib.

## Main statements

* `Martingale.indicator`: the product of a martingale with the indicator of a set that is
  measurable with respect to the first σ-algebra of the filtration is a martingale.
* `Martingale.indexComap`, `Submartingale.indexComap`: reindexing a (sub)martingale along a monotone
  map gives a (sub)martingale with respect to the filtration `Filtration.indexComap`.
* `Martingale.submartingale_convex_comp`: the composition of a martingale with a continuous convex
  function is a submartingale.
* `Martingale.submartingale_norm`: the norm of a martingale is a submartingale.
* `Submartingale.monotone_convex_comp`: the composition of a submartingale with a monotone
  continuous convex function is a submartingale.
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω E : Type*} [Preorder ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {𝓕 : Filtration ι mΩ}

section Basic

/-- Each `X t` of a martingale `X` is strongly measurable with respect to the ambient σ-algebra. -/
lemma Martingale.stronglyMeasurable' (hX : Martingale X 𝓕 P) {t : ι} :
    StronglyMeasurable (X t) :=
  hX.stronglyMeasurable t |>.mono (𝓕.le t)

/-- The indicator of a `𝓕 ⊥`-measurable set times a martingale is a martingale. -/
lemma Martingale.indicator [CompleteSpace E] [OrderBot ι] {s : Set Ω}
    (hX : Martingale X 𝓕 P) (hs : MeasurableSet[𝓕 ⊥] s) :
    Martingale (fun t ↦ s.indicator (X t)) 𝓕 P :=
  ⟨fun i ↦ (hX.stronglyAdapted i).indicator (𝓕.mono bot_le _ hs), fun i j hij ↦
    (condExp_indicator (hX.integrable _) (𝓕.mono bot_le _ hs)).trans (hX.2 i j hij).indicator⟩

end Basic

section IndexComap

variable {ι' : Type*} [Preorder ι'] {f : ι' → ι}

/-- A martingale reindexed by a monotone map is a martingale for the reindexed filtration. -/
lemma Martingale.indexComap (hX : Martingale X 𝓕 P) (hf : Monotone f) :
    Martingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.condExp_ae_eq (hf hij)⟩

/-- A submartingale reindexed by a monotone map is a submartingale for the reindexed filtration. -/
lemma Submartingale.indexComap [LE E] (hX : Submartingale X 𝓕 P) (hf : Monotone f) :
    Submartingale (X ∘ f) (𝓕.indexComap hf) P :=
  ⟨hX.stronglyAdapted.indexComap hf, fun _ _ hij ↦ hX.ae_le_condExp (hf hij),
    fun _ ↦ hX.integrable _⟩

end IndexComap

section ConvexComp

variable [CompleteSpace E] [SigmaFiniteFiltration P 𝓕] {φ : E → ℝ}

/-- The composition of a martingale with a continuous convex function is a submartingale. -/
lemma Martingale.submartingale_convex_comp (hX : Martingale X 𝓕 P)
    (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ =ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := hX.condExp_ae_eq hij |>.fun_comp φ |>.symm
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      hφ_cvx.map_condExp_le_univ (𝓕.le i) hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

/-- The norm of a martingale is a submartingale. -/
lemma Martingale.submartingale_norm (hX : Martingale X 𝓕 P) :
    Submartingale (fun t ω ↦ ‖X t ω‖) 𝓕 P :=
  hX.submartingale_convex_comp convexOn_univ_norm continuous_norm fun i ↦ (hX.integrable i).norm

/-- The composition of a submartingale with a monotone continuous convex function is a
submartingale. -/
lemma Submartingale.monotone_convex_comp [Preorder E] (hX : Submartingale X 𝓕 P)
    (hφ_mono : Monotone φ) (hφ_cvx : ConvexOn ℝ Set.univ φ) (hφ_cont : Continuous φ)
    (hφ_int : ∀ t, Integrable (fun ω ↦ φ (X t ω)) P) :
    Submartingale (fun t ω ↦ φ (X t ω)) 𝓕 P := by
  refine ⟨fun i ↦ hφ_cont.comp_stronglyMeasurable (hX.stronglyAdapted i), fun i j hij ↦ ?_, hφ_int⟩
  calc
    _ ≤ᵐ[P] fun ω ↦ φ (P[X j | 𝓕 i] ω) := (hX.ae_le_condExp hij).mono fun ω hω ↦ hφ_mono hω
    _ ≤ᵐ[P] P[fun ω ↦ φ (X j ω) | 𝓕 i] :=
      hφ_cvx.map_condExp_le_univ (𝓕.le i) hφ_cont.lowerSemicontinuous (hX.integrable j) (hφ_int j)

end ConvexComp

end MeasureTheory
