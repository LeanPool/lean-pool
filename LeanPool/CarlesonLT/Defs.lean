/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!

Definition of Fourier partial sums, multiplier class, and Carleson operator.

-/

@[expose] public noncomputable section

namespace CarlesonLT

open Real Complex Finset ENNReal MeasureTheory Set EuclideanSpace
open scoped InnerProductSpace FourierTransform

/-- The partial sums `S_N f(x) = ∑_{k = -N}^{N} f̂(k) e^{ikx}` of the Fourier series. -/
def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn two_pi_pos f n * fourier n (x : AddCircle (2 * π))

@[inherit_doc EuclideanSpace]
scoped notation "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The Carleson operator associated with a multiplier `m`. Note
we use Mathlib's Fourier transform convention here with the `2*π` in the exponent.
This does not affect boundedness statements. -/
def carlesonOperator (m : ℝ^n → ℂ) (f : ℝ^n → ℂ) (x : ℝ^n) : ℝ≥0∞ :=
  ⨆ N : ℝ^n, ‖∫ ξ, 𝓕 f ξ * 𝐞 (⟪x, ξ⟫_ℝ) * m (ξ - N)‖ₑ

/-- The weak `L²` quasinorm `‖g‖_{2,∞} = sup_{t > 0} t |{x : |g(x)| > t}|^{1/2}`. -/
def weakL2Norm {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0∞, t * μ {x | t < g x} ^ (2⁻¹ : ℝ)

/-- Anisotropic dilations `δ_λ x = (λ^{α₁} x₁, …, λ^{αₙ} xₙ)` -/
def anisoDil (α : Fin n → ℕ) (t : ℝ) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 (fun i ↦ t ^ α i * x i)

/-- The anisotropic norm `ρ(x) = max {|xᵢ|^{1/αᵢ} : i = 1, …, n}` -/
def anisoNorm (α : Fin n → ℕ) (x : ℝ^n) : ℝ := ⨆ i, |x i| ^ ((α i)⁻¹ : ℝ)

/-- Bounded, `ν` times continuously differentiable,
anisotropically homogeneous multipliers -/
structure MultiplierClass (α : Fin n → ℕ) (ν : ℕ) (m : ℝ^n → ℂ) : Prop where
  bounded : ∃ C : ℝ, ∀ ξ, ‖m ξ‖ ≤ C
  contDiffOn : ContDiffOn ℝ ν m {0}ᶜ
  homogeneous : ∀ ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → m (anisoDil α t ξ) = m ξ

/-- Multiplier norm
`‖m‖_{𝓜^ν} = sup_{|β| ≤ ν} sup_{ρ(ξ)=1} |∂^β m(ξ)|`, where `∂^β m(ξ)`
with `|β| = k` is the `k`-th derivative of `m`
evaluated at standard basis vectors `e_{i₁}, …, e_{i_k}`. -/
def multiplierNorm (α : Fin n → ℕ) (ν : ℕ) (m : ℝ^n → ℂ) : ℝ≥0∞ :=
  ⨆ (k ≤ ν) (i : Fin k → Fin n) (ξ : ℝ^n) (_ : anisoNorm α ξ = 1),
    ‖iteratedFDeriv ℝ k m ξ (fun j ↦ single (i j) 1)‖ₑ

end CarlesonLT

end
