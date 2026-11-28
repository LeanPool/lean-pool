/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The OU generator on polynomials: the Hermite eigenlayer

The spectral route to solvability diagonalises the generator instead of diagonalising the
transform. For the OU process `dX = -κX dt + σ dW`, the generator

`L p = -(κ • X) * p' + (σ²/2) • p''`

maps real polynomials to real polynomials, and on that invariant subspace the scaled
Hermite polynomials `He_n(x/s)` (with stationary scale `s² = σ²/2κ`) are eigenfunctions:
`L He_n(x/s) = -nκ He_n(x/s)` — eq. 14.16's OU case, Calc 14.14. (Since `He_n(x/s)` has
degree `n`, they diagonalise `L` on `ℝ[X]`; that basis fact is not formalized here.)
This file proves the eigenidentities by induction on `Polynomial.hermite_succ`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), together with:

* the commutator identities that drive the induction (`ouGen_derivative`, `ouGen_X_mul`);
* the Gaussian stationary no-flux condition of Calc 14.13 (`gaussianScore_ou`,
  `gaussianNoFlux_ou`) — the one-dimensional reversibility mechanism, at eval level;
* the two-mode weighted-average gap inequality (`twoMode_rate_ge_slowest`): the effective
  decay rate of a two-mode mixture is at least the slowest rate, so a one-exponential fit
  never understates mean reversion (the fit consequence itself is not formalized here).

## Status

* **Proved here:** every declaration in this file, no proof holes. The commutators carry
  the κ and σ² coefficients explicitly, and the eigeninduction closes when `σ² = 2κ`
  (only this direction is proved; the converse — that it fails off that scale — is not).
* **Not here:** that `ouGen` is the OU process's infinitesimal generator (it is defined as the
  polynomial operator above; no process appears in this file); the `L²(π)` operator theory —
  self-adjointness of the generator against the stationary law (Calc 14.13's pairing,
  eq. 14.18), the eigenfunction expansion `P_t f = Σ c_n e^{-λ_n t} φ_n` (eq. 14.17),
  completeness of the Hermite basis, spectral-gap theory beyond the two-mode inequality,
  the general-diffusion no-flux statement (only the Gaussian instance is proved), the
  swirl as a stochastic process, and the Laguerre/Jacobi rows of the Pearson table
  (no Laguerre or Jacobi polynomials are available in the library).

## Main definitions

* `ouGen`: the operator `p ↦ -(κ • X) * p' + (σ²/2) • p''` on real polynomials.
* `hermiteReal`: the probabilists' Hermite polynomial `He_n` over `ℝ`.
* `scaledHermite`: `He_n(x/s)`, as `hermiteReal n` composed with `X ↦ s⁻¹ • X`.

## Main results

* `ouGen_hermite`: `ouGen 1 (√2) (He_n) = -n • He_n`.
* `ouGen_scaledHermite`, `eval_ouGen_scaledHermite`: if `2κs² = σ²` and `s ≠ 0`, then
  `L He_n(x/s) = -nκ · He_n(x/s)`, as polynomials and pointwise.
* `ouGen_derivative`, `ouGen_X_mul`: the commutators of `ouGen` with differentiation and with
  multiplication by `X`.
* `gaussianNoFlux_ou`: at `2κs² = σ²`, `σ²/2 · π'(x) = -(κx) · π(x)` for `π(x) = exp(-x²/(2s²))`.
* `twoMode_rate_ge_slowest`: for `l₁ ≤ l₂` and positive weights, the effective decay rate of a
  two-exponential mixture is at least `l₁`.
* `swirl_isotropy`: a symmetric `2×2` solution `Σ` of `AΣ + ΣAᵀ = I` for the swirl matrix
  `A = [[1, θ], [-θ, 1]]` equals `I/2`.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 14 ("the chapter"
  throughout; eq./Calc/Ex. numbers are as there); the estimation bias is from its ch. 20.

## Tags

Ornstein–Uhlenbeck process, Hermite polynomials, generator eigenfunctions, spectral decomposition,
mean reversion, Vasicek model, MSC 60J60, MSC 91G30, JEL E43
-/

@[expose] public section

namespace MathFin.OUSpectral

open Polynomial Matrix

/-! ## The generator on polynomials -/

/-- **The OU generator as a map on real polynomials** (Calc 14.4's operator):
`L p = -(κ • X) * p.derivative + (σ²/2) • p.derivative.derivative` — drift term `-κx·p'`
plus diffusion term `(σ²/2)·p''`. Polynomial algebra only: on `Polynomial ℝ` this map is
triangular degree by degree (the drift preserves degree, the diffusion lowers it by two; not
stated as a lemma here) — which is why the chapter's polynomial moment ladder (not formalized
here) sees its diagonal eigenvalues before any eigenvectors exist. -/
noncomputable def ouGen (κ σ : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  -(κ • Polynomial.X) * p.derivative + (σ ^ 2 / 2) • p.derivative.derivative

/-- `ouGen` preserves subtraction (used by the eigeninduction: `He_{n+1} = X·He_n - He_n'`). -/
theorem ouGen_sub (κ σ : ℝ) (p q : Polynomial ℝ) :
    ouGen κ σ (p - q) = ouGen κ σ p - ouGen κ σ q := by
  simp only [ouGen, derivative_sub, ← Polynomial.C_mul']
  ring

/-! ## The commutator identities (the induction engine)

The two identities below say how the generator commutes with `d/dx` and with
multiplication by `X` — the only two operations the Hermite recursion
`hermite (n+1) = X * hermite n - derivative (hermite n)` is built from. They are stated
in their general form: the coefficients that appear are exactly `κ` and `σ²`, and the
eigeninduction closes when `σ² = 2κ` (the `s = 1` stationary scale). -/

/-- **Commutator with the derivative.** `L p' = (L p)' + κ • p'`: differentiating and
generating commute up to the drift coefficient `κ` re-supplied to the derivative term. -/
theorem ouGen_derivative (κ σ : ℝ) (p : Polynomial ℝ) :
    ouGen κ σ p.derivative = (ouGen κ σ p).derivative + κ • p.derivative := by
  simp only [ouGen, derivative_add, derivative_mul, derivative_C, derivative_X, map_neg,
    mul_one, ← Polynomial.C_mul']
  ring

/-- **Commutator with multiplication by `X`.** `L (X p) = X * L p + σ² • p' - κ • (X p)`:
multiplying by `X` and generating commute up to the creation term `σ² • p'` (the
diffusion coefficient acting on one derivative) minus the drift acting on the new
factor. -/
theorem ouGen_X_mul (κ σ : ℝ) (p : Polynomial ℝ) :
    ouGen κ σ (X * p) = X * ouGen κ σ p + σ ^ 2 • p.derivative - κ • (X * p) := by
  simp only [ouGen, derivative_mul, derivative_X, derivative_add, one_mul, ← Polynomial.C_mul']
  rw [show Polynomial.C (σ ^ 2) = Polynomial.C (σ ^ 2 / 2) + Polynomial.C (σ ^ 2 / 2) from by
    rw [← map_add]; ring_nf]
  ring

/-! ## The Hermite eigenfunctions (Calc 14.14's identity)

The unit normalization at which the eigenidentity holds with eigenvalue `-n` is the
`s = 1` stationary scale `σ² = 2κ` with `κ = 1` — spelled `ouGen 1 (Real.sqrt 2)`, i.e.
the operator `p ↦ -X * p' + p''`. This is exactly the classical Hermite ODE
`He_n'' - x He_n' = -n He_n`, so the induction is the recursion
`hermite_succ : hermite (n+1) = X * hermite n - derivative (hermite n)`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`) plus the two commutators. -/

/-- The `n`-th probabilists' Hermite polynomial over `ℝ`: `hermite n` (native to `ℤ[X]`,
`Hermite/Basic.lean`) mapped through the integer cast. At a real point `x` its
value is `He_n(x)`. -/
noncomputable def hermiteReal (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

/-- `He₀ = 1`. -/
theorem hermiteReal_zero : hermiteReal 0 = 1 := by
  simp [hermiteReal, Polynomial.hermite_zero]

/-- The Hermite recursion transported to `ℝ`: `He_{n+1} = X·He_n - He_n'`. -/
theorem hermiteReal_succ (n : ℕ) :
    hermiteReal (n + 1) = X * hermiteReal n - (hermiteReal n).derivative := by
  rw [hermiteReal, Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_X, ← Polynomial.derivative_map]
  rfl

/-- **The Hermite eigenidentity (eq. 14.16's OU case / Calc 14.14 at `κ = 1`, `s = 1`).**
The unit-normalized OU generator `ouGen 1 (Real.sqrt 2) = -X·d/dx + d²/dx²` (stationary
scale `σ² = 2κ = 2`) maps `He_n` to `-n • He_n`: the Hermite polynomials are eigenfunctions
of the OU generator with eigenvalues `-n` — the eigenvalues the chapter's triangular moment
ladder (not formalized here) finds on the diagonal, now with their eigenvectors. Induction on
`hermite_succ`; the commutators supply the two terms and the induction closes
because `σ² = 2κ` (here `2 = 2`). -/
theorem ouGen_hermite (n : ℕ) :
    ouGen 1 (Real.sqrt 2) (hermiteReal n) = -(n : ℝ) • hermiteReal n := by
  induction n with
  | zero => simp [ouGen, hermiteReal_zero]
  | succ n ih =>
    rw [hermiteReal_succ, ouGen_sub, ouGen_X_mul, ouGen_derivative, ih,
      Real.sq_sqrt (by norm_num), derivative_smul]
    simp only [one_smul, ← Polynomial.C_mul', Nat.cast_succ, map_add, map_one, map_neg,
      map_ofNat]
    ring

/-! ## The stationary scale: `He_n(x/s)` (Calc 14.14 in general position)

At the stationary scale `s² = σ²/2κ`, the eigenfunctions are the *rescaled* Hermite
polynomials `He_n(x/s)`. The chain rule for the scaling `x ↦ x/s` conjugates the general
generator into the unit one — the diffusion coefficient `σ²/2` loses exactly the factor
`s²` that the two derivatives of the scaling gain — so the unit eigenidentity transfers
with eigenvalue `-nκ` (the chapter's `L He_n = -nκ He_n`, Pearson-table OU row). -/

/-- The scaled Hermite polynomial `q_n(x) = He_n(x/s)`: `hermiteReal n` composed with the
scaling `X ↦ s⁻¹ • X`. -/
noncomputable def scaledHermite (s : ℝ) (n : ℕ) : Polynomial ℝ :=
  (hermiteReal n).comp (s⁻¹ • X)

/-- `q_n(x) = He_n(x/s)`, pointwise. -/
theorem scaledHermite_eval (n : ℕ) (x s : ℝ) :
    Polynomial.eval x (scaledHermite s n) = Polynomial.eval (x / s) (hermiteReal n) := by
  have hx : Polynomial.eval x (s⁻¹ • X) = x / s := by
    rw [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_X, div_eq_mul_inv, mul_comm]
  rw [scaledHermite, Polynomial.eval_comp, hx]

/-- The unit generator spelled out: at `κ = 1`, `σ² = 2` the OU generator is the
operator `p ↦ -(X * p') + p''` — the classical Hermite ODE operator. -/
theorem ouGen_sqrt2 (f : Polynomial ℝ) :
    ouGen 1 (Real.sqrt 2) f = -(X * f.derivative) + f.derivative.derivative := by
  rw [ouGen, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), div_self two_ne_zero]
  simp

/-- **The scaling conjugation (the chain rule for `x ↦ x/s`).** Composing with the
scaling `X ↦ s⁻¹ • X` conjugates the general generator into `κ` times the unit one:
the drift coefficient survives, and the diffusion coefficient `σ²/2` divided by the
`s²` that the two chain-rule factors contribute is exactly `κ` (this is where the
stationary-scale identity `2κs² = σ²` enters). -/
theorem ouGen_comp_smulX (κ σ s : ℝ) (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (f : Polynomial ℝ) :
    ouGen κ σ (f.comp (s⁻¹ • X))
      = κ • (ouGen 1 (Real.sqrt 2) f).comp (s⁻¹ • X) := by
  have hX : (s⁻¹ • X).derivative = Polynomial.C s⁻¹ := by
    rw [← Polynomial.C_mul', derivative_mul, derivative_C, derivative_X, zero_mul,
      zero_add, mul_one]
  have hd1 : (f.comp (s⁻¹ • X)).derivative
      = Polynomial.C s⁻¹ * f.derivative.comp (s⁻¹ • X) := by
    rw [Polynomial.derivative_comp, hX]
  have hd2 : (f.comp (s⁻¹ • X)).derivative.derivative
      = Polynomial.C (s⁻¹ * s⁻¹) * f.derivative.derivative.comp (s⁻¹ • X) := by
    rw [hd1, derivative_mul, derivative_C, zero_mul, zero_add, Polynomial.derivative_comp,
      hX, ← mul_assoc, ← map_mul]
  have hκc : σ ^ 2 / 2 * (s⁻¹ * s⁻¹) = κ := by
    rw [← h]
    field_simp
  rw [ouGen, hd2, hd1]
  simp only [← Polynomial.C_mul']
  rw [show Polynomial.C (σ ^ 2 / 2)
        * (Polynomial.C (s⁻¹ * s⁻¹)
          * (derivative (derivative f)).comp (Polynomial.C s⁻¹ * X))
      = Polynomial.C (σ ^ 2 / 2 * (s⁻¹ * s⁻¹))
        * (derivative (derivative f)).comp (Polynomial.C s⁻¹ * X) from by
      rw [← mul_assoc, ← map_mul],
    hκc, ouGen_sqrt2, Polynomial.add_comp, Polynomial.neg_comp, Polynomial.mul_comp,
    Polynomial.X_comp]
  ring

/-- **The scaled eigenidentity, polynomial level (Calc 14.14 / Pearson-table OU row).**
At the stationary scale `s² = σ²/2κ`, the generator maps the scaled Hermite polynomial
`q_n = He_n(x/s)` to `-(nκ) • q_n`. The eigenvalue is `-nκ` — the OU row of the
eigenvalue table, and the diagonal of the chapter's moment ladder (not formalized here). -/
theorem ouGen_scaledHermite {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (n : ℕ) :
    ouGen κ σ (scaledHermite s n) = (-(n : ℝ) * κ) • scaledHermite s n := by
  rw [scaledHermite, ouGen_comp_smulX κ σ s hs h, ouGen_hermite, Polynomial.smul_comp,
    smul_smul, mul_comm]

/-- **The scaled eigenidentity, eval level.** For
`q_n(x) = He_n(x/s)`: `eval x (L q_n) = -(nκ) · eval x q_n` at every point `x`. -/
theorem eval_ouGen_scaledHermite {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (n : ℕ) (x : ℝ) :
    Polynomial.eval x (ouGen κ σ (scaledHermite s n))
      = -(n : ℝ) * κ * Polynomial.eval x (scaledHermite s n) := by
  rw [ouGen_scaledHermite hs h n, Polynomial.eval_smul, smul_eq_mul]

/-- `He₂ = X² - 1` over `ℝ`. -/
theorem hermiteReal_two : hermiteReal 2 = X * X - 1 := by
  have h2 : Polynomial.hermite 2 = (X : Polynomial ℤ) * X - 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Polynomial.hermite_succ, Polynomial.hermite_one,
      derivative_X]
  rw [hermiteReal, h2]
  simp

/-- **The `n = 2` mechanism of Calc 14.14.** With `f = (x/s)² - 1` (the
evaluated `He_2(x/s)`), the generator output evaluates to `-(2κ) · f` — the drift term
preserves the degree (the chapter's text says it "lowers" it, a slip), the diffusion term
supplies exactly the constant that closes the polynomial back on itself, and the
arithmetic uses `σ²/s² = 2κ` (via the stationary-scale hypothesis). -/
theorem eval_ouGen_scaledHermite_two {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2)
    (x : ℝ) :
    Polynomial.eval x (ouGen κ σ (scaledHermite s 2))
      = -(2 : ℝ) * κ * ((x / s) ^ 2 - 1) := by
  rw [eval_ouGen_scaledHermite hs h 2 x, scaledHermite_eval, hermiteReal_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one]
  ring

/-! ## The Gaussian no-flux condition (Calc 14.13, one dimension)

The reversibility mechanism of the spectral route, at its Gaussian instance: the
stationary density `π(x) ∝ exp(-x²/(2s²))` has score `π'/π = -x/s²`, so the drift and
diffusion fluxes cancel — `(σ²/2)·π' = -κx·π` when `s² = σ²/2κ`. The score computed
below is the scale-`s` counterpart of the `n = 1` case of the Rodrigues formula
`hermite_eq_deriv_gaussian` (`Mathlib/RingTheory/Polynomial/Hermite/Gaussian.lean`, unit
scale: Hermite polynomials as Gaussian-density derivatives), proved here directly by the
chain rule; the no-flux lemma is that score times `σ²/2` under the stationary-scale
identity. -/

/-- **The Gaussian score (Calc 14.13's derivative, eval level).** The unnormalized
Gaussian density `π(x) = exp(-x²/(2s²))` satisfies `π'(x) = -(x/s²)·π(x)`: the log-density
is `-(x/s)²/2`, whose gradient `-(x/s²)` is the score. `deriv_exp` + the chain rule. (That
`π` is the OU stationary density at `s² = σ²/2κ` is not proved here.) -/
theorem gaussianScore_ou (s : ℝ) (x : ℝ) :
    deriv (fun y ↦ Real.exp (-(y ^ 2 / (2 * s ^ 2)))) x
      = -(x / s ^ 2) * Real.exp (-(x ^ 2 / (2 * s ^ 2))) := by
  have h2 : HasDerivAt (fun y ↦ -(y ^ 2 / (2 * s ^ 2))) (-(x / s ^ 2)) x := by
    have h1 := (hasDerivAt_pow 2 x).div_const (2 * s ^ 2)
    have hval : ((2 : ℕ) * x ^ (2 - 1)) / (2 * s ^ 2) = x / s ^ 2 := by
      rw [pow_one, Nat.cast_ofNat, mul_div_mul_left _ _ two_ne_zero]
    rw [hval] at h1
    exact h1.neg
  exact (h2.exp.deriv).trans (by ring)

/-- **The no-flux condition (Calc 14.13, stationary Gaussian instance).** At the
stationary scale `s² = σ²/2κ`, the drift flux `-κx·π` balances the diffusion flux
`(σ²/2)·π'`: the condition `μπ = ½(σ²π)'` that yields the divergence form (14.19)
and hence the generator's symmetry (the symmetry itself is not proved here). -/
theorem gaussianNoFlux_ou {κ σ s : ℝ} (hs : s ≠ 0) (h : 2 * κ * s ^ 2 = σ ^ 2) (x : ℝ) :
    σ ^ 2 / 2 * deriv (fun y ↦ Real.exp (-(y ^ 2 / (2 * s ^ 2)))) x
      = -(κ * x) * Real.exp (-(x ^ 2 / (2 * s ^ 2))) := by
  rw [gaussianScore_ou s x, ← h]
  field_simp

/-! ## The gap bias (the "asymptotic rate" remark, two modes)

The chapter's effective decay rate of a multimodal expansion is the weighted average
`Σ λ_n c_n e^{-λ_n t} / Σ c_n e^{-λ_n t}`. With two modes and positive weights, that
average (here with rates `l₁ ≤ l₂`) is at least the slowest rate `l₁` for every `t` — so
fitting a single exponential to a two-mode decay reads off a rate at least `l₁` and never
understates mean reversion (the chapter's second, independent route to the Bagaria ch. 20
estimation bias). Only the pointwise bound is proved here; the fitted-exponential
consequence is not formalized. -/

/-- **The two-mode gap inequality.** For rates `l₁ ≤ l₂`, positive mode weights
`0 < c₁, c₂` and any `t`, the effective decay rate of the two-mode mixture — the
weighted average of the rates, weighted by the surviving mode masses — is at least the
slowest rate `l₁`. The gap `l₂ - l₁` shows up as the excess carried by the fast mode;
the chapter's one-exponential-fit warning is a consequence of this pointwise bound (not
proved here). -/
theorem twoMode_rate_ge_slowest {l₁ l₂ c₁ c₂ t : ℝ} (hl₂ : l₁ ≤ l₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    l₁ ≤ (l₁ * c₁ * Real.exp (-(l₁ * t)) + l₂ * c₂ * Real.exp (-(l₂ * t)))
      / (c₁ * Real.exp (-(l₁ * t)) + c₂ * Real.exp (-(l₂ * t))) := by
  set E₁ := Real.exp (-(l₁ * t))
  set E₂ := Real.exp (-(l₂ * t))
  have hE₁pos : 0 < E₁ := Real.exp_pos _
  have hE₂pos : 0 < E₂ := Real.exp_pos _
  have hD : (c₁ * E₁ + c₂ * E₂) ≠ 0 :=
    (add_pos (mul_pos hc₁ hE₁pos) (mul_pos hc₂ hE₂pos)).ne'
  have hkey : 0 ≤ (l₂ - l₁) * (c₂ * E₂) :=
    mul_nonneg (sub_nonneg.2 hl₂) (mul_nonneg hc₂.le hE₂pos.le)
  field_simp
  nlinarith [hkey]

/-! ## The swirl (Ex. 14.2): matrix algebra only

The chapter's two-dimensional counterexample is the swirl `dZ = -AZ dt + dW` with
`A = [[1, θ], [-θ, 1]]`, whose antisymmetric part rotates. One fragment of it needs no process
theory: the stationary covariance is isotropic (a symmetric `Σ` with `AΣ + ΣAᵀ = I` is `½I`), so
the rotation drops out of the snapshot. In the chapter's argument this is why a snapshot cannot
detect non-reversibility; that conclusion, and the complex spectrum `-1 ± iθ` of `-A`, are not
formalized here. -/

/-- **The swirl's stationary covariance is isotropic.** Any symmetric `Σ`
solving the stationary-covariance equation `AΣ + ΣAᵀ = I` for the swirl matrix
`A = [[1, θ], [-θ, 1]]` is `½I`: the solution does not depend on the rotation `θ`, so the
snapshot carries no trace of the circulation. In the chapter's argument (Ex. 14.2) this is why a
stationary snapshot alone cannot detect that the drift is non-reversible for `θ ≠ 0` — that
non-reversibility conclusion itself is not formalized here. -/
theorem swirl_isotropy (θ a b d : ℝ)
    (h : (!![(1 : ℝ), θ; -θ, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; b, d]
        + !![a, b; b, d] * !![(1 : ℝ), -θ; θ, 1] = 1) :
    (!![(a : ℝ), b; b, d] : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(1 / 2 : ℝ), 0; 0, 1 / 2] := by
  have hM : ((!![(1 : ℝ), θ; -θ, 1] : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; b, d]
        + !![a, b; b, d] * !![(1 : ℝ), -θ; θ, 1])
      = !![2 * a + 2 * θ * b, 2 * b + θ * d - θ * a; 2 * b + θ * d - θ * a,
        2 * d - 2 * θ * b] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;> ring
  rw [hM] at h
  have e00 : 2 * a + 2 * θ * b = 1 := by simpa using congrFun (congrFun h 0) 0
  have e01 : 2 * b + θ * d - θ * a = 0 := by simpa using congrFun (congrFun h 0) 1
  have e11 : 2 * d - 2 * θ * b = 1 := by simpa using congrFun (congrFun h 1) 1
  have hkey : (1 + θ ^ 2) * b = 0 := by linear_combination (1 / 2) * e01 - (θ / 4) * (e11 - e00)
  have hb : b = 0 := (mul_eq_zero.1 hkey).resolve_left (by positivity)
  subst hb
  have ha : a = 1 / 2 := by linarith [e00]
  have hd : d = 1 / 2 := by linarith [e11]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [ha, hd]

end MathFin.OUSpectral
