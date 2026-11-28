/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Single-asset market making — closed-form (Riccati) approximation

The multi-asset Avellaneda–Stoikov market-making problem of Bergault, Evangelista, Guéant
and Vieira (*Closed-form approximations in multi-asset market making*, arXiv:1810.04383)
reduces, via a quadratic (LQ) approximation of the trade-intensity Hamiltonians, to a
Riccati system whose solution is a closed-form proxy for the value function `θ(t, q)`.

This Riccati is the LQ-**approximation** view, not the fundamental structure: for exponential
intensities the exact single-asset problem is *linearisable* by a Hopf–Cole change of variables into
a linear ODE system (Guéant–Lehalle–Fernandez-Tapia), the deeper and more faithful target (not
formalised here; the matrix-exponential derivative it needs is Mathlib's
`hasDerivAt_exp_smul_const`). We formalise the tractable approximate closed form (see
`MatrixMarketMakingRiccati` for the multi-asset analogue and the full landscape note).

Specialised here to a **single asset** (`d = 1`), we verify, in three layers:

* **Riccati coefficient** — `a(t) = Â · tanh (Â · (T − t))` solves `a' = a² − Â²` with `a(T) = 0`
  (the `tanh` derivative is derived locally — Mathlib carries none at this pin; the `T → ∞` ergodic
  limit `a(0) → Â` is a deferred follow-up).
* **Value function** — the quadratic ansatz `θ_check(t, q) = −A(t) q² − B(t) q − C(t)` solves the
  approximate Hamilton–Jacobi equation (the paper's Eq. 9) whenever `(A, B, C)` solve the
  Riccati/linear ODE system, with `A` the Riccati coefficient.
* **Quotes** — with the known exponential-intensity quote map `δ_tilde_ξ(p) = p + c`, the greedy
  bid/ask give a **constant** half-spread and an **inventory-linear** skew, for both the CARA
  (Model A) and risk-adjusted (Model B) objectives.

## Scope (mirroring `AlmgrenChriss.lean`)

We verify the closed-form solution of the **approximate** (quadratic-Hamiltonian) HJ equation. Out
of scope: the stochastic optimal-control substrate (existence/uniqueness of the true value function
solving the exact HJ equation, and the verification theorem linking `θ` to optimal quotes —
controlled marked-point-process control beyond the current pin); that the approximate value function
approximates the true one (justified numerically in the paper); the exact Hopf–Cole linearisation
(the fundamental structure; Mathlib's `hasDerivAt_exp_smul_const` covers the matrix-exponential
calculus it needs, so what is missing is the construction itself); and deriving `δ_tilde_ξ` from the
intensity sup (it is defined by its known closed form from Guéant [18] /
Guéant–Lehalle–Fernandez-Tapia [20]). The multi-asset **approximate** matrix Riccati is now
discharged in `MatrixMarketMakingRiccati`.

## Main definitions

* `riccatiCoeff`: the scalar Riccati coefficient `a(t) = Â · tanh (Â · (T − t))`.
* `expIntensityQuote`: the exponential-intensity quote map `δ_tilde(p) = p + c`.
* `quoteConstA`, `quoteConstB`: the constants `c = log (1 + γ z / k) / (γ z)` (CARA objective) and
  `c = 1 / k` (risk-adjusted objective).
* `mmQuoteBid`, `mmQuoteAsk`: the greedy bid and ask quotes `δ_tilde(2A(t)q + A(t)z + B(t))` and
  `δ_tilde(−2A(t)q + A(t)z − B(t))`.

## Main results

* `hasDerivAt_tanh`: `tanh' x = 1 − tanh² x`.
* `riccatiCoeff_terminal`, `hasDerivAt_riccatiCoeff`: `a(T) = 0` and `a' = a² − Â²`.
* `valueFunction_satisfies_approxHJ`: if `A`, `B`, `C` have the stated derivatives, the quadratic
  ansatz `−A(s) q² − B(s) q − C(s)` has time-derivative equal to the approximate
  Hamilton–Jacobi right-hand side, for `z > 0`.
* `mmHalfSpread_const`: `(δ_checkᵃ + δ_checkᵇ)/2 = A(t)·z + c`, independent of the inventory `q`.
* `mmSkew_linear`: `(δ_checkᵃ − δ_checkᵇ)/2 = −2·A(t)·q − B(t)`.

## References

* [Bergault et al., *Closed-form approximations in multi-asset market
  making*][BergaultEtAlMarketMaking], Prop. 1; §3.3.3
* [Guéant, Lehalle and Fernandez-Tapia][GueantLehalleFernandezTapia]

## Tags

Avellaneda–Stoikov, market making, Riccati equation, Hamilton–Jacobi–Bellman, optimal quotes,
inventory risk, bid-ask spread, MSC 91G80, MSC 49L20, JEL G14
-/

@[expose] public section

namespace MathFin

open Real

/-! ## §1  Abstract scalar Riccati coefficient -/

/-- **Derivative of `tanh`** — `tanh'(x) = 1 − tanh² x` — derived from `tanh = sinh / cosh` and the
    quotient rule (Mathlib carries no `HasDerivAt` lemma for `tanh` at this pin). -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hsinh : HasDerivAt Real.sinh (Real.cosh x) x := by simpa using (hasDerivAt_id x).sinh
  have hcosh : HasDerivAt Real.cosh (Real.sinh x) x := by simpa using (hasDerivAt_id x).cosh
  have hfun : Real.tanh = Real.sinh / Real.cosh := by
    funext y; simp [Real.tanh_eq_sinh_div_cosh]
  have hval : (1 : ℝ) - Real.tanh x ^ 2
      = (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp
  rw [hval, hfun]
  exact hsinh.div hcosh hc

/-- **Scalar Riccati coefficient** `a(t) = Â · tanh (Â · (T − t))` — the closed-form solution of the
    normalised Riccati equation `a' = a² − Â²` with terminal value `a(T) = 0`. In the market-making
    instance, `Â = σ · √(γ · (α₂ᵇ + α₂ᵃ) · z)` and the value-function coefficient is
    `A(t) = riccatiCoeff Â T t / (2 · (α₂ᵇ + α₂ᵃ) · z)`. -/
noncomputable def riccatiCoeff (Â T t : ℝ) : ℝ := Â * Real.tanh (Â * (T - t))

/-- **Terminal condition**: `a(T) = 0`. -/
theorem riccatiCoeff_terminal (Â T : ℝ) : riccatiCoeff Â T T = 0 := by
  unfold riccatiCoeff
  rw [sub_self, mul_zero, Real.tanh_zero, mul_zero]

/-- **Riccati ODE**: `a'(t) = a(t)² − Â²`. -/
theorem hasDerivAt_riccatiCoeff (Â T t : ℝ) :
    HasDerivAt (riccatiCoeff Â T) (riccatiCoeff Â T t ^ 2 - Â ^ 2) t := by
  unfold riccatiCoeff
  have h_inner : HasDerivAt (fun s : ℝ => Â * (T - s)) (-Â) t := by
    have h_id : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub T
    simpa using h_id.const_mul Â
  have h := ((hasDerivAt_tanh (Â * (T - t))).comp t h_inner).const_mul Â
  simp only [Function.comp_def] at h
  rw [show (Â * Real.tanh (Â * (T - t))) ^ 2 - Â ^ 2
        = Â * ((1 - Real.tanh (Â * (T - t)) ^ 2) * -Â) by ring]
  exact h

/-! ## §2  Value-function verification of the approximate Hamilton–Jacobi equation (d = 1) -/

/-- **Value-function verification (Prop. 1, `d = 1`).** The quadratic ansatz
    `θ_check(t, q) = −A(t) q² − B(t) q − C(t)` has time-derivative equal to the
    algebraic right-hand side of the approximate Hamilton–Jacobi equation
    (the paper's Eq. 9, `Q = ∞`) whenever `(A, B, C)`
    solve the scalar reduction of the ODE system (Eq. 11) — `A` the Riccati coefficient
    (`Â = σ · √(γ · (α₂ᵇ + α₂ᵃ) · z)`). The `B`/`C` ODE right-hand sides are pinned by the `ring`
    closure below (self-certifying). -/
theorem valueFunction_satisfies_approxHJ
    (γ σ z α₀b α₁b α₂b α₀a α₁a α₂a : ℝ) (hz : 0 < z)
    (A B C : ℝ → ℝ) (t q : ℝ)
    (hA : HasDerivAt A (2 * z * (α₂b + α₂a) * A t ^ 2 - γ * σ ^ 2 / 2) t)
    (hB : HasDerivAt B (2 * z * (α₁b - α₁a) * A t + 2 * z ^ 2 * (α₂b - α₂a) * A t ^ 2
                        + 2 * z * (α₂b + α₂a) * A t * B t) t)
    (hC : HasDerivAt C (z * (α₀b + α₀a) + z ^ 2 * (α₁b + α₁a) * A t + z * (α₁b - α₁a) * B t
                        + z ^ 3 * (α₂b + α₂a) * A t ^ 2 / 2 + z * (α₂b + α₂a) * B t ^ 2 / 2
                        + z ^ 2 * (α₂b - α₂a) * A t * B t) t) :
    HasDerivAt (fun s => -(A s) * q ^ 2 - B s * q - C s)
      (γ * σ ^ 2 / 2 * q ^ 2 - z * (α₀b + α₀a)
        - α₁b * (2 * A t * q * z + A t * z ^ 2 + B t * z)
        - α₁a * (-2 * A t * q * z + A t * z ^ 2 - B t * z)
        - (1 / (2 * z)) * (α₂b * (2 * A t * q * z + A t * z ^ 2 + B t * z) ^ 2
                    + α₂a * (-2 * A t * q * z + A t * z ^ 2 - B t * z) ^ 2)) t := by
  have hz' : z ≠ 0 := hz.ne'
  have h2z : (2 : ℝ) * z ≠ 0 := by positivity
  have hθ : HasDerivAt (fun s => -(A s) * q ^ 2 - B s * q - C s)
      (-(2 * z * (α₂b + α₂a) * A t ^ 2 - γ * σ ^ 2 / 2) * q ^ 2
        - (2 * z * (α₁b - α₁a) * A t + 2 * z ^ 2 * (α₂b - α₂a) * A t ^ 2
           + 2 * z * (α₂b + α₂a) * A t * B t) * q
        - (z * (α₀b + α₀a) + z ^ 2 * (α₁b + α₁a) * A t + z * (α₁b - α₁a) * B t
           + z ^ 3 * (α₂b + α₂a) * A t ^ 2 / 2 + z * (α₂b + α₂a) * B t ^ 2 / 2
           + z ^ 2 * (α₂b - α₂a) * A t * B t)) t :=
    ((hA.neg.mul_const (q ^ 2)).sub (hB.mul_const q)).sub hC
  convert hθ using 1
  field_simp
  ring

/-! ## §3  Closed-form quotes — constant spread + inventory-linear skew (Models A & B) -/

/-- **Exponential-intensity quote map** `δ_tilde_ξ(p) = p + c` (Guéant [18] / GLFT [20]); `c` is the
model
    constant (`quoteConstA`/`quoteConstB`). Defined, not re-derived from the intensity sup. -/
noncomputable def expIntensityQuote (c p : ℝ) : ℝ := p + c

/-- **Model-A (CARA, `ξ = γ`) quote constant** `c = (1 / (γ z)) · log (1 + γ z / k)`. -/
noncomputable def quoteConstA (γ z k : ℝ) : ℝ := 1 / (γ * z) * Real.log (1 + γ * z / k)

/-- **Model-B (risk-adjusted, `ξ = 0`) quote constant** `c = 1 / k`. -/
noncomputable def quoteConstB (k : ℝ) : ℝ := 1 / k

/-- **Greedy bid quote** `δ_checkᵇ = δ_tilde(2 A(t) q + A(t) z + B(t))` (from `Δ⁺ / z`). -/
noncomputable def mmQuoteBid (A B : ℝ → ℝ) (z c t q : ℝ) : ℝ :=
  expIntensityQuote c (2 * A t * q + A t * z + B t)

/-- **Greedy ask quote** `δ_checkᵃ = δ_tilde(−2 A(t) q + A(t) z − B(t))` (from `Δ⁻ / z`). -/
noncomputable def mmQuoteAsk (A B : ℝ → ℝ) (z c t q : ℝ) : ℝ :=
  expIntensityQuote c (-2 * A t * q + A t * z - B t)

/-- **Constant half-spread**: `(δ_checkᵃ + δ_checkᵇ) / 2 = A(t) · z + c`,
    independent of inventory `q`. This holds for both models via the constant `c`
    (`quoteConstA` for Model A, `quoteConstB` for Model B). -/
theorem mmHalfSpread_const (A B : ℝ → ℝ) (z c t q : ℝ) :
    (mmQuoteAsk A B z c t q + mmQuoteBid A B z c t q) / 2 = A t * z + c := by
  unfold mmQuoteAsk mmQuoteBid expIntensityQuote; ring

/-- **Inventory-linear skew**: `(δ_checkᵃ − δ_checkᵇ) / 2 = −2 · A(t) · q − B(t)`
    (the constant `c` cancels). -/
theorem mmSkew_linear (A B : ℝ → ℝ) (z c t q : ℝ) :
    (mmQuoteAsk A B z c t q - mmQuoteBid A B z c t q) / 2 = -2 * A t * q - B t := by
  unfold mmQuoteAsk mmQuoteBid expIntensityQuote; ring

end MathFin
