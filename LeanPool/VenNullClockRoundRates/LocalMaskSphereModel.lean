/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AbPh project (AI-generated Lean proofs)
-/

-- Modified for Lean Pool: adapted the imports and reused the shared sphere model.

module

public import LeanPool.VenNullClockRoundRates.SphereModel

/-! The finite-menu observation interface for the shared unit-sphere model. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace VenMask

/-- The exponential read kernel for one control in a finite menu. -/
def sphereKernel {n : ℕ} (x s : Fin n → ℝ) (θ : ℝ) (i : Fin n) (y : UnitSphere) : ℝ :=
  Real.exp (x i * firstEnergy y + s i * secondEnergy θ y)

/-- At every nonaligned angle, with any fixed list of distinct strength pairs,
one strictly positive hidden log-focusing suffices at each nearby angle to
match *all* of the reference mean reads exactly. The multiplier is an analytic
angular function (constant plus finite combinations of exponential kernels). -/
def SphereMaskingCertificate : Prop :=
  ∀ {n : ℕ} (μ : Measure UnitSphere) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (x s : Fin n → ℝ) (θ₀ w₀ : ℝ),
    1 < w₀ → Real.sin θ₀ ≠ 0 → Function.Injective (fun i ↦ (x i, s i)) →
    ∀ᶠ θ in 𝓝 θ₀, ∃ c : Fin n → ℝ,
      let k := sphereKernel x s
      let w := fun y ↦ w₀ + ∑ j, c j * k θ j y
      (∀ y, 1 < w y) ∧
      (∀ i, (∫ y, w y * k θ i y ∂μ) = ∫ y, w₀ * k θ₀ i y ∂μ)
end VenMask
