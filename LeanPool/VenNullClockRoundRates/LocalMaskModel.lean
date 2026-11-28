/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Instances.Matrix

/-! Finite scalar reads as integrals of angular kernels against a common
multiplier. The number of distinct controls is arbitrary and finite.
A parameter may change the angle or other features of the kernel. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped Topology
namespace VenMask

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- The integrated weighted response of one control in the finite menu. -/
def read (μ : Measure Ω) (k : Fin n → Ω → ℝ) (w : Ω → ℝ) (i : Fin n) : ℝ :=
  ∫ y, w y * k i y ∂μ

/-- The finite linear combination of menu kernels with the given coefficients. -/
def synthesis (k : Fin n → Ω → ℝ) (c : Fin n → ℝ) (y : Ω) : ℝ :=
  ∑ j, c j * k j y

/-- The Gram matrix of the finite menu kernels under the observation measure. -/
def gram (μ : Measure Ω) (k : Fin n → Ω → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ ∫ y, k j y * k i y ∂μ

/-- Linear independence in the measured angular domain, not assumed
invertibility of the response matrix. The condition excludes redundant controls. -/
def AEIndependent (μ : Measure Ω) (k : Fin n → Ω → ℝ) : Prop :=
  ∀ c, synthesis k c =ᵐ[μ] 0 → c = 0

/-- Exact local masking. For every nearby parameter there is a multiplier,
strictly above one everywhere, matching every original scalar read exactly.
The multiplier is exhibited as a constant plus a finite linear combination of
the new kernels; smooth kernels therefore give smooth multipliers. -/
def LocalMaskingCertificate : Prop :=
  ∀ {Ω Z : Type} [MeasurableSpace Ω] [TopologicalSpace Z] {n : ℕ}
    (μ : Measure Ω) (k : Z → Fin n → Ω → ℝ) (z₀ : Z) (w₀ B : ℝ),
    1 < w₀ →
    (∀ᶠ z in 𝓝 z₀, ∀ i y, |k z i y| ≤ B) →
    (∀ᶠ z in 𝓝 z₀, ∀ i, Integrable (k z i) μ) →
    (∀ᶠ z in 𝓝 z₀, ∀ i j, Integrable (fun y ↦ k z j y * k z i y) μ) →
    AEIndependent μ (k z₀) →
    ContinuousAt (fun z ↦ gram μ (k z)) z₀ →
    ContinuousAt (fun z ↦ read μ (k z) (fun _ ↦ w₀)) z₀ →
    ∀ᶠ z in 𝓝 z₀, ∃ c : Fin n → ℝ,
      (∀ y, 1 < w₀ + synthesis (k z) c y) ∧
      read μ (k z) (fun y ↦ w₀ + synthesis (k z) c y) =
        read μ (k z₀) (fun _ ↦ w₀)
/-- The angular quadrupole energies of the lineage can be supplied for F,G.
An open patch in their joint image at the reference angle is the geometric
nondegeneracy condition. No moment independence is assumed in this version. -/
def kernel (x s : Fin n → ℝ) (F G : Ω → ℝ) (i : Fin n) (y : Ω) : ℝ :=
  Real.exp (x i * F y + s i * G y)

/-- Local masking for bounded continuous exponential kernels with distinct controls and an open
reference image. -/
def ExponentialMaskingCertificate : Prop :=
  ∀ {Ω Z : Type} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [TopologicalSpace Z] [FirstCountableTopology Z] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (x s : Fin n → ℝ) (F G : Z → Ω → ℝ) (z₀ : Z) (w₀ : ℝ),
    1 < w₀ →
    Function.Injective (fun i ↦ (x i, s i)) →
    (∃ p : ℝ × ℝ, Set.range (fun y ↦ (F z₀ y, G z₀ y)) ∈ 𝓝 p) →
    (∀ z, Continuous (F z) ∧ Continuous (G z)) →
    (∀ y, ContinuousAt (fun z ↦ F z y) z₀ ∧ ContinuousAt (fun z ↦ G z y) z₀) →
    (∀ z y, |F z y| ≤ 1 ∧ |G z y| ≤ 1) →
    ∀ᶠ z in 𝓝 z₀, ∃ c : Fin n → ℝ,
      (∀ y, 1 < w₀ + synthesis (kernel x s (F z) (G z)) c y) ∧
      read μ (kernel x s (F z) (G z))
        (fun y ↦ w₀ + synthesis (kernel x s (F z) (G z)) c y) =
        read μ (kernel x s (F z₀) (G z₀)) (fun _ ↦ w₀)
end VenMask
