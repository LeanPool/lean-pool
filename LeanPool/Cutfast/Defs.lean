/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Definitions of the advertised statements (generated from `Challenge.lean`)

Advertised statements of the formalization of the paper *On the cutoff phenomenon for fast
diffusion and porous medium equations* by D. Chafaï, M. Fathi and N. Simonov (arXiv:2503.11770;
corrected source `cutfast-lean.tex`). This file is the small, trusted statement
surface: every definition below has its ordinary mathematical meaning, documented in its
docstring, and the theorems state the results of the paper.

For a dimension `d` and an exponent `m > 0`, `m ≠ 1`, the paper considers the
Fokker–Planck version `∂ₜv = Δ(vᵐ) + div(x v)` of `∂ₜu = Δ(uᵐ)` with Dirac initial data at
`x₀ ∈ ℝᵈ`, whose solution is explicit (eq. (FDEFPv)):
`v(t,x) = s(t)^{-αd} B((x - e^{-t}x₀) / s(t)^α)` with `s(t) = α(1 - e^{-t/α})`,
`α = 1/(2 - d(1-m))`, and `B` the Barenblatt profile
`B(x) = (c + α(1-m)/(2m)|x|²)₊^{1/(m-1)}` normalized to be a probability density.
The equilibrium is `v_∞(x) = α^{-αd} B(x / α^α)` (eq. (vinf)).

The main results (Theorems 1.1 and 1.2 of the paper) state that, in high dimension, the
quadratic Wasserstein distance `W₂²`, the relative entropy `Hₘ` and the Fisher information
`Iₘ` between `v(t)` and `v_∞`, maximized over `|x₀| ≤ r√d`, collapse abruptly from `+∞`
to `0` around the critical time `max(1,α)/2 · log d` (resp. `1/2 · log d` for fixed `m > 1`).

The file also states the remaining mathematical claims of the paper: the solution `u` of
`∂ₜu = Δ(uᵐ)` and the time change linking it to `v`, the initial and long-time behavior, the
moment condition and the infinite Wasserstein distance for heavy tails, the entropy dissipation
identity, the Bregman form of the entropy, the diffusion limit `m → 1`, other sizes of the set of
initial points (Section 1.4.3), Lemmas 2.1–4.2, and Remarks 3.2 (Student t-distributions) and 4.3
(projections of uniform laws on spheres). Some claims of the paper are corrected here; see
`ERRATA.md`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

/-- The Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The exponent `α = 1 / (2 - d(1-m))` of the self-similar scaling (eq. (B)). -/
noncomputable def alpha (d : ℕ) (m : ℝ) : ℝ := 1 / (2 - d * (1 - m))

/-- The Barenblatt profile with a free constant `c`:
`B_c(x) = (c + α(1-m)/(2m) |x|²)₊ ^ (1/(m-1))` (eq. (B)). -/
noncomputable def barenblattWith (d : ℕ) (m c : ℝ) (x : E d) : ℝ :=
  (max (c + alpha d m * (1 - m) / (2 * m) * ‖x‖ ^ 2) 0) ^ (1 / (m - 1))

/-- The normalizing constant `c = c_{d,m} > 0` of the Barenblatt profile: a constant `c > 0`
such that `B_c` is a probability density function (it exists and is unique, see
`barenblattConst_spec`); the junk value `0` is used if there is none. -/
noncomputable def barenblattConst (d : ℕ) (m : ℝ) : ℝ :=
  open Classical in
  if h : ∃ c : ℝ, 0 < c ∧ Integrable (barenblattWith d m c) ∧ ∫ x, barenblattWith d m c x = 1
  then h.choose else 0

/-- The Barenblatt probability density function `B = B_{c_{d,m}}` (eq. (B)). -/
noncomputable def barenblatt (d : ℕ) (m : ℝ) (x : E d) : ℝ :=
  barenblattWith d m (barenblattConst d m) x

/-- The solution `v(t,x)` of the Fokker–Planck fast diffusion / porous medium equation
`∂ₜv = Δ(vᵐ) + div(x v)` with initial condition `δ_{x₀}` (eq. (FDEFPv)):
`v(t,x) = (α(1-e^{-t/α}))^{-αd} B((x - e^{-t}x₀) / (α(1-e^{-t/α}))^α)`. -/
noncomputable def solution (d : ℕ) (m : ℝ) (x₀ : E d) (t : ℝ) (x : E d) : ℝ :=
  ((alpha d m * (1 - exp (-t / alpha d m))) ^ (alpha d m * d))⁻¹ *
    barenblatt d m (((alpha d m * (1 - exp (-t / alpha d m))) ^ alpha d m)⁻¹ •
      (x - exp (-t) • x₀))

/-- The equilibrium `v_∞(x) = lim_{t→∞} v(t,x) = α^{-αd} B(x / α^α)` (eq. (vinf)). -/
noncomputable def equilibrium (d : ℕ) (m : ℝ) (x : E d) : ℝ :=
  (alpha d m ^ (alpha d m * d))⁻¹ * barenblatt d m ((alpha d m ^ alpha d m)⁻¹ • x)

/-- The measure `f(x) dx` with density `f` with respect to the Lebesgue measure of `ℝᵈ`. -/
noncomputable def densityMeasure {d : ℕ} (f : E d → ℝ) : Measure (E d) :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

/-- The squared quadratic Monge–Kantorovich–Wasserstein distance
`W₂²(μ,ν) = inf_π ∫ |x-y|² dπ(x,y)`, the infimum over all couplings `γ` of `μ` and `ν`
(probability measures on `ℝᵈ × ℝᵈ` with marginals `μ` and `ν`), with values in `[0,∞]`. -/
noncomputable def wassersteinSq {d : ℕ} (μ ν : Measure (E d)) : ℝ≥0∞ :=
  ⨅ (γ : Measure (E d × E d)) (_ : IsProbabilityMeasure γ)
    (_ : γ.map Prod.fst = μ) (_ : γ.map Prod.snd = ν), ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ

/-- The integrand of the relative entropy (free energy) `Hₘ(f | g)` of eq. (tsalis):
`(f(x)ᵐ - g(x)ᵐ - (1-m)/2 |x|² (f(x) - g(x))) / (m-1)`. -/
noncomputable def relEntropyDensity {d : ℕ} (m : ℝ) (f g : E d → ℝ) (x : E d) : ℝ :=
  (f x ^ m - g x ^ m - (1 - m) / 2 * ‖x‖ ^ 2 * (f x - g x)) / (m - 1)

/-- The relative entropy (free energy) of eq. (tsalis):
`Hₘ(f | g) = 1/(m-1) ∫ (f(x)ᵐ - g(x)ᵐ - (1-m)/2 |x|² (f(x) - g(x))) dx`. -/
noncomputable def relEntropy {d : ℕ} (m : ℝ) (f g : E d → ℝ) : ℝ :=
  ∫ x, relEntropyDensity m f g x

/-- The Fisher information (entropy production) of eq. (fisher), relative to the
equilibrium `v_∞` (which enters through the confinement `x`):
`Iₘ(f | v_∞) = ∫ f(x) |x + m/(m-1) ∇(f^{m-1})(x)|² dx`, with values in `[0,∞]`. -/
noncomputable def fisherInfo {d : ℕ} (m : ℝ) (f : E d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x * ‖x + (m / (m - 1)) • gradient (fun y => f y ^ (m - 1)) x‖ ^ 2)

/-- The exponent `m = ((d-2)α + 1)/(dα)` attached to a fixed `α` in dimension `d`
(Theorem 1.1); equivalently `α = 1/(2 - d(1-m))`. -/
noncomputable def exponentOfAlpha (α : ℝ) (d : ℕ) : ℝ := ((d - 2) * α + 1) / (d * α)

/-- The solution `u(t,x) = t^{-αd} B((x - x₀)/t^α)` of `∂ₜu = Δ(uᵐ)` with `u(0,·) = δ_{x₀}`
(eq. (sol)). -/
noncomputable def fdeSolution (d : ℕ) (m : ℝ) (x₀ : E d) (t : ℝ) (x : E d) : ℝ :=
  (t ^ (alpha d m * d))⁻¹ * barenblatt d m ((t ^ alpha d m)⁻¹ • (x - x₀))

/-- The normalizing constant of the full-space Barenblatt profile (eq. (Bxc)):
`c = (π^{d/2} Γ(p - d/2) / (b^{d/2} Γ(p)))^{2/(2p-d)}`. -/
noncomputable def fullBarenblattConst (d : ℕ) (p b : ℝ) : ℝ :=
  (π ^ ((d : ℝ) / 2) * Gamma (p - d / 2) / (b ^ ((d : ℝ) / 2) * Gamma p)) ^ (2 / (2 * p - d))

/-- The full-space Barenblatt profile with shape `p` and scale `b` (eq. (Bxc)):
`B(x) = (c + b|x|²)^{-p}` with `c = fullBarenblattConst d p b`. -/
noncomputable def fullBarenblatt (d : ℕ) (p b : ℝ) (x : E d) : ℝ :=
  (fullBarenblattConst d p b + b * ‖x‖ ^ 2) ^ (-p)

/-- The normalizing constant of the compactly supported Barenblatt profile (eq. (CBxc)):
`c = (b^{d/2} Γ(p+1+d/2) / (π^{d/2} Γ(p+1)))^{2/(2p+d)}`. -/
noncomputable def compactBarenblattConst (d : ℕ) (p b : ℝ) : ℝ :=
  (b ^ ((d : ℝ) / 2) * Gamma (p + 1 + d / 2) / (π ^ ((d : ℝ) / 2) * Gamma (p + 1))) ^
    (2 / (2 * p + d))

/-- The compactly supported Barenblatt profile with shape `p` and scale `b` (eq. (CBxc)):
`B(x) = (c - b|x|²)₊ᵖ` with `c = compactBarenblattConst d p b`. -/
noncomputable def compactBarenblatt (d : ℕ) (p b : ℝ) (x : E d) : ℝ :=
  (max (compactBarenblattConst d p b - b * ‖x‖ ^ 2) 0) ^ p

/-- The density of the multivariate Student t-distribution with position `x₀`, `r > 0` degrees of
freedom and (positive definite) scale matrix `Σ`:
`x ↦ C (1 + (x-x₀)ᵀΣ⁻¹(x-x₀)/r)^{-(r+d)/2}` with `C = Γ((r+d)/2) / (Γ(r/2) √det(rπΣ))`. -/
noncomputable def studentDensity (d : ℕ) (r : ℝ) (x₀ : E d) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : E d) : ℝ :=
  Gamma ((r + d) / 2) / (Gamma (r / 2) * √(((r * π) • S).det)) *
    (1 + ⟪x - x₀, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ (x - x₀)⟫_ℝ / r) ^ (-((r + d) / 2))

/-- The density of the Fisher–Snedecor F-distribution with `(d₁, d₂)` degrees of freedom:
`x ↦ (d₁/d₂)^{d₁/2} x^{d₁/2-1} (1 + d₁x/d₂)^{-(d₁+d₂)/2} / B(d₁/2, d₂/2)` on `(0,∞)`. -/
noncomputable def fisherSnedecorDensity (d₁ d₂ x : ℝ) : ℝ :=
  if 0 < x then
    (d₁ / d₂) ^ (d₁ / 2) * x ^ (d₁ / 2 - 1) * (1 + d₁ / d₂ * x) ^ (-((d₁ + d₂) / 2)) /
      (Gamma (d₁ / 2) * Gamma (d₂ / 2) / Gamma ((d₁ + d₂) / 2))
  else 0

/-- The uniform probability distribution on the centered sphere of radius `R` of `ℝᵈ`: the
normalized surface measure (Mathlib's `Measure.toSphere` of the Lebesgue measure, pushed
forward by `x ↦ R x`). -/
noncomputable def sphereUniform (d : ℕ) (R : ℝ) : Measure (E d) :=
  ((volume : Measure (E d)).toSphere Set.univ)⁻¹ •
    (volume : Measure (E d)).toSphere.map (fun x : sphere (0 : E d) 1 => R • (x : E d))

/-- The projection `(x₁, …, x_d) ↦ (x₁, …, x_n)` of `ℝᵈ` onto its first `n` coordinates. -/
noncomputable def projFirst {n d : ℕ} (h : n ≤ d) (x : E d) : E n :=
  WithLp.toLp 2 (fun i => x (Fin.castLE h i))

/-- The stereographic projection `x ↦ (x₁, …, x_{d-1}) / (1 - x_d)` from the unit sphere of `ℝᵈ`
(minus its north pole) onto `ℝ^{d-1}`. -/
noncomputable def stereoProj {d : ℕ} (hd : 1 ≤ d) (x : E d) : E (d - 1) :=
  (1 - x ⟨d - 1, Nat.sub_lt hd Nat.one_pos⟩)⁻¹ • projFirst (Nat.sub_le d 1) x

end Cutfast
