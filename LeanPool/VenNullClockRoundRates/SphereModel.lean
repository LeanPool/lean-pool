/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! Coordinate-fixed pair of axes in the physical round generator sphere:
first axis (1, 0, 0), second (cos θ, sin θ, 0). The measure may be the normalized
area law. The conclusion concerns scalar exponential reads, not a PDE. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology
namespace VenMask
/-- The Cartesian unit sphere used by the scalar observation model. -/
def UnitSphere := {q : ℝ × ℝ × ℝ // q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = 1}
deriving instance TopologicalSpace, MeasurableSpace for UnitSphere

/-- Quadrupole energy as a function of the coordinate along the axis. -/
def energy (u : ℝ) : ℝ := (1 - u ^ 2) ^ 2

/-- Energy for the first axis, aligned with the first Cartesian coordinate. -/
def firstEnergy (y : UnitSphere) : ℝ := energy y.val.1

/-- Energy for the second axis rotated in the first two coordinates by `θ`. -/
def secondEnergy (θ : ℝ) (y : UnitSphere) : ℝ :=
  energy (Real.cos θ * y.val.1 + Real.sin θ * y.val.2.1)

/-- Unweighted exponential observation kernel for a finite list of controls. -/
def sphereKernel {n : ℕ} (x s : Fin n → ℝ) (θ : ℝ) (i : Fin n) (y : UnitSphere) : ℝ :=
  Real.exp (x i * firstEnergy y + s i * secondEnergy θ y)

/-- At every nonaligned angle, with any fixed list of distinct strength pairs,
one strictly positive hidden log - focusing suffices at each nearby angle to
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
