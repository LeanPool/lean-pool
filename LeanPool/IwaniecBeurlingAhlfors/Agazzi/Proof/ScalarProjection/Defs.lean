/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# §2, Lemma 4: the objects

The objects of Lemma 4 (TeX lines 400–405), and the representation choices of the formalization:

* `W^{1,∞}_per (Q)` is represented by the Lipschitz `ℤ²`-periodic functions `ℝ² → ℝ` (`LipPer`):
  every class of `W^{1,∞}_per (Q)` has exactly one Lipschitz representative, and the gradient of a
  Lipschitz function is its pointwise derivative almost everywhere (Rademacher).
* `Dξ (x)` is `sgrad ξ x = (∂₁ ξ (x), ∂₂ ξ (x))`, from the Fréchet derivative (`0` where `ξ` is not
  differentiable).
* "almost everywhere" is with respect to Lebesgue measure on the unit square, the torus `Q`.
* `constraintSet K p` is `𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`.
* the `L² (Q)`-projection `ζ` of `η` on `𝒞` is a minimizer of `ξ ↦ ∫_Q (η − ξ)²` on `𝒞`
  (`IsL2Projection`): the point of `𝒞` nearest to `η` in `L² (Q)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Agazzi

/-- The gradient `Dξ (x) = (∂₁ ξ (x), ∂₂ ξ (x))` of `ξ : ℝ² → ℝ` (`0` where `ξ` is not
differentiable). -/
def sgrad (ξ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => fderiv ℝ ξ x (Pi.single j 1)

/-- `W^{1,∞}_per (Q)`, by Lipschitz representatives: `ξ` is Lipschitz and `ℤ²`-periodic. -/
def LipPer (ξ : (Fin 2 → ℝ) → ℝ) : Prop :=
  (∃ C : NNReal, LipschitzWith C ξ) ∧ IsPeriodic ξ

/-- `𝒞 = {ξ ∈ W^{1,∞}_per (Q) : p + Dξ ∈ K a.e.}`. -/
def constraintSet (K : Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Set ((Fin 2 → ℝ) → ℝ) :=
  {ξ | LipPer ξ ∧ ∀ᵐ x ∂(volume.restrict unitSquare), p + sgrad ξ x ∈ K}

/-- `ζ` is an `L² (Q)`-projection of `η` on `𝒞`: `ζ ∈ 𝒞` and
`∫_Q (η − ζ)² ≤ ∫_Q (η − ξ)²` for every `ξ ∈ 𝒞`. -/
def IsL2Projection (𝒞 : Set ((Fin 2 → ℝ) → ℝ)) (η ζ : (Fin 2 → ℝ) → ℝ) : Prop :=
  ζ ∈ 𝒞 ∧ ∀ ξ ∈ 𝒞, ∫ x in unitSquare, (η x - ζ x) ^ 2 ≤ ∫ x in unitSquare, (η x - ξ x) ^ 2

end Agazzi
