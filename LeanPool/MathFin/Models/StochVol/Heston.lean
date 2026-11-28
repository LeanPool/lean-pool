/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.CIRRiccati
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# The Heston affine transform at the generator/PDE level (2D)

The 2D Heston state is (x, v) = (log-spot, variance) with

`dS = rS dt + √v S dW¹`,  `dv = κ(θ − v) dt + ξ √v dW²`,  `d⟨W¹, W²⟩ = ρ dt`,

so x = log S obeys `dx = (r − v/2) dt + √v dW¹` (Itô) and the generator on test
functions `f : ℝ → ℝ → ℝ` is

`Lf = (r − v/2) ∂_x f + κ(θ − v) ∂_v f + (v/2) ∂_xx f + ρ ξ v ∂_xv f + (ξ² v/2) ∂_vv f`
(`hestonGenerator`; the cross term `ρ ξ v ∂_xv` is the new 2D piece, carrying the
correlation; at the generator level it is pure calculus).

The recipe is Bagaria ch. 14, Prop 14.5 (invariance test `Lu/u ∈ span{gᵢ}`) and eq. 14.4 (`L
e^(φ+ψx) = [μ(x)(ψ + ½ v(x) ψ²)] e^(φ+ψx)`). The 2D reading-off: with exponent-gradient
`(Bx, Bv) = (u, ψ)`, the bracket of the generator lemma below is `(c₀ + c₁ v)` with the
**x-coefficient identically zero** — the third Riccati equation `Bx' = 0` (the log-spot gradient is
conserved). Matching `∂_t Φ + LΦ = 0` (the *backward* pricing equation; Bagaria's Calc 14.6 states
the forward form `∂_t u = Lu`, same matching with negated coefficients, the flip
`affineBondPrice_solves_pde` in `Models/Rates/AffineTermStructurePDE` also makes) gives the
**calendar-time** system

`Bx' = 0`,  `Bv' = u/2 − u²/2 + (κ − ρξu) Bv − (ξ²/2) Bv²`,  `A' = −r·u − κθ·Bv`,

with terminal data `Bx(T) = u`, `Bv(T) = 0`, `A(T) = 0` (payoff `e^{u x}`). In
maturity time `τ = T − t` the `Bv`-equation is the constant-forced Riccati

`b̂' = ½(u² − u) + (ρξu − κ) b̂ + ½ξ² b̂²`,  `b̂(0) = 0`  (`hasDerivAt_hestonBv`),

the Calc 14.6 ψ-equation `ψ' = bψ + ½dψ²` plus the constant `½(u² − u)` produced by the x-row of the
drift (the coupling `−v/2` of variance into log-spot); `â' = ru + κθ b̂` (`hasDerivAt_hestonA`). The
real moment `M(u) = E[e^{u log S_T}]` is the transform at real `u`; the characteristic function is
the same system at `iu` — the complex route is out of scope here.

The closed forms are the Möbius members

`b̂(τ) = (u² − u)(e^{γτ} − 1) / ((γ + κ − ρξu)e^{γτ} + (γ − κ + ρξu))`,
`γ = √((κ − ρξu)² + ξ²(u − u²))`  (the ρ-shifted CIR root: `cirGamma`'s
`√(κ² + 2ξ²)` under `κ ↦ κ − ρξu` plus the u-dependent piece),

`â(τ) = ruτ + (2κθ/ξ²)[((γ + κ − ρξu)/2)τ − log(D(τ)/(2γ))]`,  `D` the shared
denominator. The ODE residuals vanish after the single substitution
`γ² = (κ − ρξu)² + ξ²(u − u²)`.

The `Bv`-equation has a constant term `½(u² − u)` and the quadratic sign `+½ξ²ψ²` of
the characteristic-function side, so it is neither the CIR bond `B`-factor
(`B' = 1 − κB − (ξ²/2)B²`, `Models.Rates.CIRRiccati`) nor a constant-free Bernoulli
equation; its Möbius solution is derived here by the quotient rule, one coefficient
rewrite, `field_simp` and `ring`.

**Guards — the admissible strip.** The CIR discriminant `κ² + 2ξ²` is always
nonnegative; the Heston discriminant
`γ² = (κ − ρξu)² + ξ²(u − u²)` is **not** always nonnegative (it → −∞ as
u → ±∞ when |ρ| < 1): off the strip the closed form silently degenerates (γ = 0 in
Lean's `Real.sqrt`) and is *false* as an ODE solution. This is Bagaria's Thm 14.7
proviso made concrete — the Riccati explosion / moment-existence strip. The flow
lemmas below take the clean sufficient hypothesis `0 < u < 1`, `ξ ≠ 0`, which
forces `γ > |κ − ρξu|`, hence `D(τ) > 0` for **all** real τ (no per-τ guard);
`κ` and `θ` enter the flow facts with no hypotheses at all (the deterministic layer
needs no Feller-type condition).

**Not proved.** That the profile at `(0, x₀, v₀)` equals `E[e^{u log S_T}]` is not
proved: it needs a Heston process (existence of the square-root SDE, unbounded
coefficients) and the 2D correlated Itô formula, neither of which the library has. This
module is the generator/PDE level only.

## Main definitions

* `expAffine`, `expAffine2`: the exponential-affine families `e^(φ + ψ x)` and
  `e^(A + Bx·x + Bv·v)`.
* `hestonGenerator`: the generator
  `Lf = (r − v/2) ∂_x f + κ(θ − v) ∂_v f + (v/2) ∂_xx f + ρξv ∂_xv f + (ξ²v/2) ∂_vv f` on test
  functions of (log-spot, variance).
* `hestonGamma`: the root `γ = √((κ − ρξu)² + ξ²(u − u²))`.
* `hestonBvDenom`: the Möbius denominator `D(τ) = (γ + κ − ρξu)e^{γτ} + (γ − κ + ρξu)`.
* `hestonBv`: the closed form `b̂(τ) = (u² − u)(e^{γτ} − 1) / D(τ)`.
* `hestonA`: the closed form `â(τ) = ruτ + (2κθ/ξ²)[((γ + κ − ρξu)/2)τ − log(D(τ)/(2γ))]`.
* `hestonProfile`: the candidate transform profile `e^{A(t) + u·x + B(t)·v}`.

## Main results

* `hestonGenerator_expAffine2`: the generator applied to `expAffine2 A Bx Bv` is an affine
  function of `v` times `expAffine2 A Bx Bv`.
* `hestonBracket_xFree`: the multiplier `L E / E` depends on `v` alone.
* `hestonGamma_eq_cirGamma`: for `0 ≤ u ≤ 1`, `hestonGamma` is `cirGamma` at mean reversion
  `κ − ρξu` and volatility `ξ√((u − u²)/2)`.
* `hestonBvDenom_pos`: for `ξ ≠ 0` and `0 < u < 1`, `D(τ) > 0` for every real `τ`.
* `hasDerivAt_hestonBv`: for `ξ ≠ 0` and `0 < u < 1`, `hestonBv` solves the Riccati equation
  `b̂' = (u² − u)/2 + (ρξu − κ) b̂ + (ξ²/2) b̂²` with `b̂(0) = 0` (`hestonBv_at_zero`).
* `hasDerivAt_hestonA`: under the same hypotheses, `â' = r u + κθ b̂`.
* `hasDerivAt_hestonBvCalendar`, `hasDerivAt_hestonACalendar`: the same flows in calendar time
  `t ↦ b̂(T − t)`, `t ↦ â(T − t)`.
* `hestonProfile_pde`: for any `A, B` solving the calendar-time Riccati system,
  `∂_t Φ + LΦ = 0` for `Φ = hestonProfile`.
* `hestonTransform_pde`, `hestonTransform_terminal`: for `ξ ≠ 0` and `0 < u < 1`, the profile
  built from `hestonA` and `hestonBv` solves `∂_t Φ + LΦ = 0` and equals `e^{u x}` at `t = T`.
  The identification of the profile with `E[e^{u log S_T}]` for a Heston process is not
  proved.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 14, Prop 14.5
* [Heston, *A closed-form solution for options with stochastic volatility with applications to bond
  and currency options*][Heston1993]

## Tags

Heston model, stochastic volatility, affine transform, Riccati equation, characteristic function,
generator PDE, MSC 91G20, MSC 60J60, JEL G13
-/

@[expose] public section

namespace MathFin.Heston

/-! ### The 1D exponential-affine family -/

/-- The exponential-affine family `x ↦ e^(φ + ψ x)` (Bagaria ch. 14, eq. 14.4). -/
noncomputable def expAffine (φ ψ x : ℝ) : ℝ := Real.exp (φ + ψ * x)

/-- The affine inner function `y ↦ φ + ψ * y` has derivative `ψ`. -/
theorem hasDerivAt_affine (φ ψ x : ℝ) : HasDerivAt (fun y => φ + ψ * y) ψ x := by
  simpa using ((hasDerivAt_id x).const_mul ψ).const_add φ

/-- Second derivative of the exponential-affine family: `ψ² * e^(φ + ψ x)`. -/
theorem deriv_deriv_expAffine (φ ψ : ℝ) :
    deriv (deriv (expAffine φ ψ)) = fun x => ψ ^ 2 * expAffine φ ψ x := by
  have h1 : deriv (expAffine φ ψ) = fun x => Real.exp (φ + ψ * x) * ψ :=
    funext fun x => (hasDerivAt_affine φ ψ x).exp.deriv
  funext x
  rw [h1, ((hasDerivAt_affine φ ψ x).exp.mul_const ψ).deriv]
  simp only [expAffine]
  ring

/-! ### The 2D exponential-affine family and its partial derivatives -/

/-- The 2D exponential-affine family `E_{A,Bx,Bv}(x,v) = e^(A + Bx·x + Bv·v)`,
curried so that each partial derivative is a 1D derivative of an `expAffine` member. -/
noncomputable def expAffine2 (A Bx Bv x v : ℝ) : ℝ := Real.exp (A + Bx * x + Bv * v)

/-- x-frozen bridge: `E_{A,Bx,Bv}(·, v)` is the 1D member `expAffine (A + Bv·v) Bx`. -/
theorem expAffine2_left (A Bx Bv v : ℝ) :
    (fun y => expAffine2 A Bx Bv y v) = expAffine (A + Bv * v) Bx := by
  funext y
  change Real.exp (A + Bx * y + Bv * v) = Real.exp ((A + Bv * v) + Bx * y)
  exact Real.exp_eq_exp.mpr (by ring)

/-- v-frozen bridge: `E_{A,Bx,Bv}(x, ·)` is the 1D member `expAffine (A + Bx·x) Bv`. -/
theorem expAffine2_right (A Bx Bv x : ℝ) :
    expAffine2 A Bx Bv x = expAffine (A + Bx * x) Bv := by
  funext w
  change Real.exp (A + Bx * x + Bv * w) = Real.exp ((A + Bx * x) + Bv * w)
  exact Real.exp_eq_exp.mpr (by ring)

/-- ∂_x of the 2D family: `Bx · E`. -/
theorem hasDerivAt_expAffine2_x (A Bx Bv x v : ℝ) :
    HasDerivAt (fun y => expAffine2 A Bx Bv y v) (Real.exp (A + Bx * x + Bv * v) * Bx) x := by
  rw [expAffine2_left A Bx Bv v]
  have h := (hasDerivAt_affine (A + Bv * v) Bx x).exp
  rw [show (A + Bv * v) + Bx * x = A + Bx * x + Bv * v from by ring] at h
  exact h

/-- ∂_v of the 2D family: `Bv · E`. -/
theorem hasDerivAt_expAffine2_v (A Bx Bv x v : ℝ) :
    HasDerivAt (expAffine2 A Bx Bv x) (Real.exp (A + Bx * x + Bv * v) * Bv) v := by
  rw [expAffine2_right A Bx Bv x]
  exact (hasDerivAt_affine (A + Bx * x) Bv v).exp

/-- ∂_x of the 2D family (function form). -/
theorem deriv_expAffine2_x (A Bx Bv v : ℝ) :
    deriv (fun y => expAffine2 A Bx Bv y v)
      = fun y => Real.exp (A + Bx * y + Bv * v) * Bx :=
  funext fun y => (hasDerivAt_expAffine2_x A Bx Bv y v).deriv

/-- ∂_v of the 2D family (function form). -/
theorem deriv_expAffine2_v (A Bx Bv x : ℝ) :
    deriv (expAffine2 A Bx Bv x) = fun w => Real.exp (A + Bx * x + Bv * w) * Bv :=
  funext fun w => (hasDerivAt_expAffine2_v A Bx Bv x w).deriv

/-- ∂_xx of the 2D family (function form): `Bx² · E`. -/
theorem deriv_deriv_expAffine2_x (A Bx Bv v : ℝ) :
    deriv (deriv (fun y => expAffine2 A Bx Bv y v))
      = fun y => Real.exp (A + Bx * y + Bv * v) * Bx ^ 2 := by
  rw [expAffine2_left A Bx Bv v, deriv_deriv_expAffine]
  funext y
  simp only [expAffine]
  rw [show (A + Bv * v) + Bx * y = A + Bx * y + Bv * v from by ring]
  ring

/-- ∂_vv of the 2D family (function form): `Bv² · E`. -/
theorem deriv_deriv_expAffine2_v (A Bx Bv x : ℝ) :
    deriv (deriv (expAffine2 A Bx Bv x))
      = fun w => Real.exp (A + Bx * x + Bv * w) * Bv ^ 2 := by
  rw [expAffine2_right A Bx Bv x, deriv_deriv_expAffine]
  funext w
  simp only [expAffine]
  ring

/-- The mixed derivative ∂_v∂_x (function form): `Bx·Bv · E` — the genuinely 2D
piece, computed as the v-derivative of the x-derivative. -/
theorem deriv_expAffine2_xv (A Bx Bv x : ℝ) :
    deriv (fun w => deriv (fun y => expAffine2 A Bx Bv y w) x)
      = fun w => Real.exp (A + Bx * x + Bv * w) * (Bx * Bv) := by
  have hfun : ∀ w, deriv (fun y => expAffine2 A Bx Bv y w) x
      = Real.exp (A + Bx * x + Bv * w) * Bx :=
    fun w => (hasDerivAt_expAffine2_x A Bx Bv x w).deriv
  have hderiv : ∀ w, HasDerivAt (fun z => Real.exp (A + Bx * x + Bv * z) * Bx)
      (Real.exp (A + Bx * x + Bv * w) * (Bx * Bv)) w := by
    intro w
    have h := ((hasDerivAt_affine (A + Bx * x) Bv w).exp).mul_const Bx
    rw [show (A + Bx * x) + Bv * w = A + Bx * x + Bv * w from rfl,
      show Real.exp (A + Bx * x + Bv * w) * Bv * Bx
        = Real.exp (A + Bx * x + Bv * w) * (Bx * Bv) from by ring] at h
    exact h
  funext w
  simp only [hfun]
  exact (hderiv w).deriv

/-! ### The Heston generator on the exponential-affine family -/

/-- The **Heston generator** on test functions `f : ℝ → ℝ → ℝ` (x = log-spot,
v = variance):
`Lf = (r − v/2) ∂_x f + κ(θ − v) ∂_v f + (v/2) ∂_xx f + ρξv ∂_xv f + (ξ²v/2) ∂_vv f`
— the correlated 2D generator of `dx = (r − v/2)dt + √v dW¹`,
`dv = κ(θ − v)dt + ξ√v dW²`, `d⟨W¹,W²⟩ = ρdt` (the covariance matrix is
`v · [[1, ρξ], [ρξ, ξ²]]`, so the mixed generator term is `a₁₂ = ρξv`). -/
noncomputable def hestonGenerator (r κ θ ξ ρ : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x v =>
    (r - v / 2) * deriv (fun y => f y v) x
    + κ * (θ - v) * deriv (f x) v
    + v / 2 * deriv (deriv (fun y => f y v)) x
    + ρ * ξ * v * deriv (fun w => deriv (fun y => f y w) x) v
    + ξ ^ 2 * v / 2 * deriv (deriv (f x)) v

/-- **The generator on the 2D family.** The Heston generator applied to a member of the 2D
exponential-affine family is an affine-in-`v` bracket times the function itself:

`L E = ((r·Bx + κθ·Bv) + (Bx²/2 + ρξ·Bx·Bv + ξ²Bv²/2 − κBv − Bx/2)·v) · E`

— Bagaria ch. 14, eq. 14.4 in the 2D Heston roles: drift `(r − v/2, κ(θ − v))` and
covariance `v·[[1, ρξ], [ρξ, ξ²]]` are both affine in `(x, v)`, so the bracket is
affine (in fact x-free). The cross term `ρξ·Bx·Bv` inside the v-coefficient is the
new 2D content. -/
theorem hestonGenerator_expAffine2 (r κ θ ξ ρ A Bx Bv : ℝ) :
    hestonGenerator r κ θ ξ ρ (expAffine2 A Bx Bv)
      = fun x v => ((r * Bx + κ * θ * Bv)
          + (Bx ^ 2 / 2 + ρ * ξ * Bx * Bv + ξ ^ 2 / 2 * Bv ^ 2 - κ * Bv - Bx / 2) * v)
          * Real.exp (A + Bx * x + Bv * v) := by
  funext x v
  simp only [hestonGenerator]
  rw [deriv_deriv_expAffine2_x A Bx Bv v, deriv_deriv_expAffine2_v A Bx Bv x,
    deriv_expAffine2_xv A Bx Bv x, deriv_expAffine2_x A Bx Bv v,
    deriv_expAffine2_v A Bx Bv x]
  ring

/-- **The 2D invariance (bracket) corollary.** The bracket of `hestonGenerator_expAffine2` is
affine in `v` with intercept `c₀ = r·Bx + κθ·Bv` and slope
`c₁ = Bx²/2 + ρξ·Bx·Bv + ξ²Bv²/2 − κBv − Bx/2`. Matching the backward pricing
equation `∂_tΦ + LΦ = 0` against `∂_tΦ/Φ = A' + Bx'·x + Bv'·v` reads off the
Heston Riccati system for the `(A, Bx, Bv)` triple: `A' = −c₀`, `Bv' = −c₁`, and
(the x-row) `Bx' = 0` — see `hestonBracket_xFree`. -/
theorem hestonBracket_affine (r κ θ ξ ρ A Bx Bv : ℝ) :
    ∃ (c₀ c₁ : ℝ), c₀ = r * Bx + κ * θ * Bv
      ∧ c₁ = Bx ^ 2 / 2 + ρ * ξ * Bx * Bv + ξ ^ 2 / 2 * Bv ^ 2 - κ * Bv - Bx / 2
      ∧ hestonGenerator r κ θ ξ ρ (expAffine2 A Bx Bv)
          = fun x v => (c₀ + c₁ * v) * expAffine2 A Bx Bv x v := by
  refine ⟨r * Bx + κ * θ * Bv,
    Bx ^ 2 / 2 + ρ * ξ * Bx * Bv + ξ ^ 2 / 2 * Bv ^ 2 - κ * Bv - Bx / 2, rfl, rfl, ?_⟩
  rw [hestonGenerator_expAffine2]
  funext x v
  simp only [expAffine2]

/-- **The x-free bracket** — the multiplier `L E / E` is a function of `v` alone.
The vanishing x-coefficient is the third Riccati equation: the log-spot gradient
`Bx` is conserved along the transform flow (this is why Heston's transform has a
fixed `u·x` term and only `(A, Bv)` move). -/
theorem hestonBracket_xFree (r κ θ ξ ρ A Bx Bv : ℝ) :
    ∃ (g : ℝ → ℝ), ∀ x v,
      hestonGenerator r κ θ ξ ρ (expAffine2 A Bx Bv) x v = g v * expAffine2 A Bx Bv x v := by
  refine ⟨fun v => (r * Bx + κ * θ * Bv)
      + (Bx ^ 2 / 2 + ρ * ξ * Bx * Bv + ξ ^ 2 / 2 * Bv ^ 2 - κ * Bv - Bx / 2) * v, ?_⟩
  intro x v
  rw [hestonGenerator_expAffine2]
  simp only [expAffine2]

/-! ### The Riccati flow (maturity time): the ρ-shifted Möbius closed forms

The `Bv`-equation `b̂' = ½(u² − u) + (ρξu − κ)b̂ + ½ξ²b̂²` is the general
constant-forced Riccati `b' = c + b₁b + db²` (`c = ½(u²−u)`, `b₁ = ρξu − κ`,
`d = ½ξ²`) — Calc 14.6's ψ-equation plus the x-row's constant. Its linearization
(Calc 14.10's substitution) has characteristic roots `(b₁ ± γ)/2` with
`γ² = b₁² − 4cd = (κ − ρξu)² + ξ²(u − u²)` — the ρ-shifted `cirGamma`. The
Möbius member solving it from `b̂(0) = 0` is derived like `cirBondB`
in `Models/Rates/CIRRiccati` (partial fractions against the fixed points, `b(0) = 0` imposed); the
`â`-antiderivative integrates `κθ·b̂` in closed form (log of the shared
denominator), mirroring `cirBondA`.

Guards (module header): the strip `0 < u < 1`, `ξ ≠ 0` forces `γ > |κ − ρξu|` and
`D(τ) > 0` for all real `τ`; `κ, θ` carry no hypotheses. -/

/-- The Heston characteristic root `γ = √((κ − ρξu)² + ξ²(u − u²))` — `cirGamma`'s
`√(κ² + 2ξ²)` with the ρ-shifted mean reversion `κ ↦ κ − ρξu` and the
moment-dependent piece. -/
noncomputable def hestonGamma (κ ξ ρ u : ℝ) : ℝ :=
  Real.sqrt ((κ - ρ * ξ * u) ^ 2 + ξ ^ 2 * (u - u ^ 2))

/-- **Heston's root is the CIR root, shifted.** For `0 ≤ u ≤ 1`, the Heston characteristic root
is `cirGamma` (`Models/Rates/CIRRiccati.lean`) at mean reversion `κ − ρξu` and volatility
`ξ√((u − u²)/2)`. -/
theorem hestonGamma_eq_cirGamma (κ ξ ρ : ℝ) {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) :
    hestonGamma κ ξ ρ u = cirGamma (κ - ρ * ξ * u) (ξ * Real.sqrt ((u - u ^ 2) / 2)) := by
  have h : 0 ≤ (u - u ^ 2) / 2 := by nlinarith
  rw [hestonGamma, cirGamma, mul_pow, Real.sq_sqrt h]
  ring_nf

/-- The shared Möbius denominator `D(τ) = (γ + κ − ρξu)e^{γτ} + (γ − κ + ρξu)`
(positive on the strip for every real `τ`). -/
noncomputable def hestonBvDenom (κ ξ ρ u τ : ℝ) : ℝ :=
  (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * Real.exp (hestonGamma κ ξ ρ u * τ)
    + (hestonGamma κ ξ ρ u - κ + ρ * ξ * u)

/-- The **Heston `Bv`-flow** (maturity time): the explicit Möbius solution of
`b̂' = ½(u² − u) + (ρξu − κ)b̂ + ½ξ²b̂²`, `b̂(0) = 0`:

`b̂(τ) = (u² − u)(e^{γτ} − 1) / D(τ)`. -/
noncomputable def hestonBv (κ ξ ρ u τ : ℝ) : ℝ :=
  (u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) / hestonBvDenom κ ξ ρ u τ

/-- The **Heston `A`-flow** (maturity time): the explicit antiderivative of
`ru + κθ·b̂` vanishing at `τ = 0`:

`â(τ) = ruτ + (2κθ/ξ²)[((γ + κ − ρξu)/2)τ − log(D(τ)/(2γ))]`

(the integral of the Möbius flow is the log of the shared denominator — the
linearization identity `b̂ = −(2/ξ²)(log w)'` with `w = e^{λ₋τ}D(τ)/(2γ)`). -/
noncomputable def hestonA (r κ θ ξ ρ u τ : ℝ) : ℝ :=
  r * u * τ + (2 * κ * θ / ξ ^ 2)
    * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2 * τ
        - Real.log (hestonBvDenom κ ξ ρ u τ / (2 * hestonGamma κ ξ ρ u)))

/-! #### γ-plumbing (private) -/

private theorem hestonGamma_sq (κ ξ ρ u : ℝ) (hu1 : 0 < u) (hu2 : u < 1) :
    hestonGamma κ ξ ρ u ^ 2 = (κ - ρ * ξ * u) ^ 2 + ξ ^ 2 * (u - u ^ 2) := by
  have hpos : 0 < u * (1 - u) := mul_pos hu1 (by linarith)
  have h1 : 0 < u - u ^ 2 := by nlinarith [hpos]
  have h3 : 0 ≤ ξ ^ 2 * (u - u ^ 2) := mul_nonneg (sq_nonneg ξ) h1.le
  have hnng : 0 ≤ (κ - ρ * ξ * u) ^ 2 + ξ ^ 2 * (u - u ^ 2) := by
    linarith [sq_nonneg (κ - ρ * ξ * u), h3]
  rw [pow_two, hestonGamma, Real.mul_self_sqrt hnng]

private theorem hestonGamma_pos (κ ξ ρ u : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    0 < hestonGamma κ ξ ρ u := by
  refine Real.sqrt_pos.mpr ?_
  have hpos : 0 < u * (1 - u) := mul_pos hu1 (by linarith)
  have h1 : 0 < ξ ^ 2 * (u - u ^ 2) := by
    have := mul_pos (sq_pos_of_ne_zero hξ) (by nlinarith [hpos])
    nlinarith [this]
  have h2 : 0 ≤ (κ - ρ * ξ * u) ^ 2 := sq_nonneg _
  nlinarith

private theorem hestonGamma_ne_zero (κ ξ ρ u : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    hestonGamma κ ξ ρ u ≠ 0 :=
  ne_of_gt (hestonGamma_pos κ ξ ρ u hξ hu1 hu2)

private theorem hestonGamma_abs_lt (κ ξ ρ u : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    κ - ρ * ξ * u < hestonGamma κ ξ ρ u ∧ -(κ - ρ * ξ * u) < hestonGamma κ ξ ρ u := by
  have hγpos : 0 < hestonGamma κ ξ ρ u := hestonGamma_pos κ ξ ρ u hξ hu1 hu2
  have hsq : (κ - ρ * ξ * u) ^ 2 < hestonGamma κ ξ ρ u ^ 2 := by
    rw [hestonGamma_sq κ ξ ρ u hu1 hu2]
    have hpos : 0 < u * (1 - u) := mul_pos hu1 (by linarith)
    have hp : 0 < ξ ^ 2 * (u - u ^ 2) := by
      have := mul_pos (sq_pos_of_ne_zero hξ) (by nlinarith [hpos])
      nlinarith [this]
    linarith
  have hab := abs_lt.mp (abs_lt_of_sq_lt_sq hsq hγpos.le)
  constructor
  · linarith [hab.2]
  · linarith [hab.1]

/-- The shared denominator is positive on the strip, for **every** real `τ`
(no per-τ guard: both coefficients `γ ± (κ − ρξu)` are positive and `e^{γτ} > 0`). -/
theorem hestonBvDenom_pos (κ ξ ρ u τ : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    0 < hestonBvDenom κ ξ ρ u τ := by
  obtain ⟨h1, h2⟩ := hestonGamma_abs_lt κ ξ ρ u hξ hu1 hu2
  exact add_pos (mul_pos (by linarith) (Real.exp_pos _)) (by linarith)

/-- Terminal data of the `Bv`-flow: `b̂(0) = 0` (definitional — the numerator
vanishes; no guard needed). -/
theorem hestonBv_at_zero (κ ξ ρ u : ℝ) : hestonBv κ ξ ρ u 0 = 0 := by
  simp only [hestonBv, mul_zero, Real.exp_zero, sub_self, mul_zero, zero_div]

/-- Terminal data of the `A`-flow: `â(0) = 0` (the linear terms die and the log
sees `D(0)/(2γ) = 2γ/(2γ) = 1`; guard `γ ≠ 0`). -/
theorem hestonA_at_zero (r κ θ ξ ρ u : ℝ) (hγ : hestonGamma κ ξ ρ u ≠ 0) :
    hestonA r κ θ ξ ρ u 0 = 0 := by
  have hD0 : hestonBvDenom κ ξ ρ u 0 = 2 * hestonGamma κ ξ ρ u := by
    simp only [hestonBvDenom, mul_zero, Real.exp_zero, mul_one]
    ring
  have h2γ : (2 : ℝ) * hestonGamma κ ξ ρ u ≠ 0 :=
    mul_ne_zero (by norm_num) hγ
  simp only [hestonA, mul_zero, hD0]
  rw [div_self h2γ, Real.log_one, sub_self, mul_zero, add_zero]

/-- **The `Bv` Riccati ODE.** The Möbius closed form solves
`b̂' = ½(u² − u) + (ρξu − κ)b̂ + ½ξ²b̂²` — the Calc 14.6 ψ-equation in the Heston
roles with the x-row's constant. Proof: as `hasDerivAt_cirBondB`
(quotient rule, the coefficient rewrite `ξ²/2 = ((κ−ρξu)² − γ²)/(2(u²−u))` from
`γ² = (κ−ρξu)² + ξ²(u−u²)`, then `field_simp`/`ring`; the residual is a polynomial
identity). -/
theorem hasDerivAt_hestonBv (κ ξ ρ u τ : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    HasDerivAt (hestonBv κ ξ ρ u)
      ((u ^ 2 - u) / 2 + (ρ * ξ * u - κ) * hestonBv κ ξ ρ u τ
        + ξ ^ 2 / 2 * hestonBv κ ξ ρ u τ ^ 2) τ := by
  have hc : ξ ^ 2 * (u ^ 2 - u) = (κ - ρ * ξ * u) ^ 2 - hestonGamma κ ξ ρ u ^ 2 := by
    rw [hestonGamma_sq κ ξ ρ u hu1 hu2]
    ring
  -- derivative building blocks
  have hlin : HasDerivAt (fun s : ℝ => hestonGamma κ ξ ρ u * s) (hestonGamma κ ξ ρ u) τ := by
    simpa using (hasDerivAt_id τ).const_mul (hestonGamma κ ξ ρ u)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (hestonGamma κ ξ ρ u * s))
      (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u) τ := by
    simpa using hlin.exp
  have hnum : HasDerivAt (fun s : ℝ => (u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * s) - 1))
      ((u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u)) τ := by
    simpa using (hexp.sub_const 1).const_mul (u ^ 2 - u)
  have hden : HasDerivAt (fun s : ℝ => (hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
        * Real.exp (hestonGamma κ ξ ρ u * s) + (hestonGamma κ ξ ρ u - κ + ρ * ξ * u))
      ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
        * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u)) τ := by
    simpa using (hexp.const_mul (hestonGamma κ ξ ρ u + κ - ρ * ξ * u)).fun_add
      (hasDerivAt_const τ (hestonGamma κ ξ ρ u - κ + ρ * ξ * u))
  have hDne : hestonBvDenom κ ξ ρ u τ ≠ 0 :=
    ne_of_gt (hestonBvDenom_pos κ ξ ρ u τ hξ hu1 hu2)
  have hD2 : hestonBvDenom κ ξ ρ u τ ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  have hq := hnum.div hden hDne
  -- the value identity, cleared deterministically: strip the outer `D²`, expand the
  -- remaining products, then one `linear_combination` with the γ-relation `hc`
  -- (multiplier `−(u²−u)(E−1)²/2`)
  have hval :
      (((u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u) *
          ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * Real.exp (hestonGamma κ ξ ρ u * τ) +
            (hestonGamma κ ξ ρ u - κ + ρ * ξ * u)) -
        (u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) *
          ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
            * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u))) /
        ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * Real.exp (hestonGamma κ ξ ρ u * τ) +
          (hestonGamma κ ξ ρ u - κ + ρ * ξ * u)) ^ 2)
      = (u ^ 2 - u) / 2 + (ρ * ξ * u - κ) * hestonBv κ ξ ρ u τ
        + ξ ^ 2 / 2 * hestonBv κ ξ ρ u τ ^ 2 := by
    rw [show ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * Real.exp (hestonGamma κ ξ ρ u * τ)
          + (hestonGamma κ ξ ρ u - κ + ρ * ξ * u)) = hestonBvDenom κ ξ ρ u τ from rfl,
      show hestonBv κ ξ ρ u τ = (u ^ 2 - u)
          * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) / hestonBvDenom κ ξ ρ u τ from rfl]
    rw [div_eq_iff hD2]
    have hR : ((u ^ 2 - u) / 2 + (ρ * ξ * u - κ)
          * ((u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1)
            / hestonBvDenom κ ξ ρ u τ)
          + ξ ^ 2 / 2 * ((u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1)
            / hestonBvDenom κ ξ ρ u τ) ^ 2) * hestonBvDenom κ ξ ρ u τ ^ 2
        = (u ^ 2 - u) * hestonBvDenom κ ξ ρ u τ ^ 2 / 2 + (ρ * ξ * u - κ) * (u ^ 2 - u)
            * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) * hestonBvDenom κ ξ ρ u τ
          + ξ ^ 2 / 2 * (u ^ 2 - u) ^ 2 * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) ^ 2 := by
      rw [div_pow]
      field_simp [hDne]
    rw [hR]
    simp only [hestonBvDenom]
    linear_combination (-(u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) ^ 2 / 2) * hc
  rw [hval] at hq
  exact hq

/-- **The `A`-flow ODE.** `â' = r·u + κθ·b̂` — the integral half of the Riccati
system (`φ' = aψ + ½cψ²`, eq. 14.5, in the Heston roles: the x-row contributes
`r·u`, the v-row `κθ·b̂`). Proof: the `hasDerivAt_cirBondA` idiom — the log's
derivative via `.div_const` + `.log`, cleaned by the key lemma
`(γ + κ − ρξu)(D(τ) − 2γe^{γτ}) = ξ²(u² − u)(e^{γτ} − 1)` (pure ring after the
γ-relation). Guard: the strip. -/
theorem hasDerivAt_hestonA (r κ θ ξ ρ u τ : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u) (hu2 : u < 1) :
    HasDerivAt (hestonA r κ θ ξ ρ u) (r * u + κ * θ * hestonBv κ ξ ρ u τ) τ := by
  have hγpos : 0 < hestonGamma κ ξ ρ u := hestonGamma_pos κ ξ ρ u hξ hu1 hu2
  have hγne : hestonGamma κ ξ ρ u ≠ 0 := ne_of_gt hγpos
  have hDne : hestonBvDenom κ ξ ρ u τ ≠ 0 :=
    ne_of_gt (hestonBvDenom_pos κ ξ ρ u τ hξ hu1 hu2)
  have hDne' : (hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
        * Real.exp (hestonGamma κ ξ ρ u * τ) + (hestonGamma κ ξ ρ u - κ + ρ * ξ * u)
      ≠ 0 := hDne
  have hξ2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ
  have hpos : 0 < u * (1 - u) := mul_pos hu1 (by linarith)
  have hnlt : u ^ 2 - u < 0 := by nlinarith [hpos]
  have hc : ξ ^ 2 * (u ^ 2 - u) = (κ - ρ * ξ * u) ^ 2 - hestonGamma κ ξ ρ u ^ 2 := by
    rw [hestonGamma_sq κ ξ ρ u hu1 hu2]
    ring
  -- the key lemma (folded denominator as an atom): the linearization identity
  have hkey : (hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
        * (hestonBvDenom κ ξ ρ u τ - 2 * hestonGamma κ ξ ρ u
            * Real.exp (hestonGamma κ ξ ρ u * τ))
      = ξ ^ 2 * (u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1) := by
    simp only [hestonBvDenom]
    rw [hc]
    ring
  -- derivative building blocks
  have hlin : HasDerivAt (fun s : ℝ => hestonGamma κ ξ ρ u * s) (hestonGamma κ ξ ρ u) τ := by
    simpa using (hasDerivAt_id τ).const_mul (hestonGamma κ ξ ρ u)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (hestonGamma κ ξ ρ u * s))
      (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u) τ := by
    simpa using hlin.exp
  have hterm1 : HasDerivAt (fun s : ℝ => r * u * s) (r * u) τ := by
    simpa using (hasDerivAt_id τ).const_mul (r * u)
  have hterm2 : HasDerivAt (fun s : ℝ => (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2 * s)
      ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2) τ := by
    simpa using (hasDerivAt_id τ).const_mul ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2)
  have hdenf : HasDerivAt (fun s : ℝ => (hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
        * Real.exp (hestonGamma κ ξ ρ u * s) + (hestonGamma κ ξ ρ u - κ + ρ * ξ * u))
      ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
        * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u)) τ := by
    simpa using (hexp.const_mul (hestonGamma κ ξ ρ u + κ - ρ * ξ * u)).fun_add
      (hasDerivAt_const τ (hestonGamma κ ξ ρ u - κ + ρ * ξ * u))
  have h2γ : (2 : ℝ) * hestonGamma κ ξ ρ u ≠ 0 := mul_ne_zero (by norm_num) hγne
  have hdiv := hdenf.div_const (2 * hestonGamma κ ξ ρ u)
  have hdivne : hestonBvDenom κ ξ ρ u τ / (2 * hestonGamma κ ξ ρ u) ≠ 0 :=
    div_ne_zero hDne h2γ
  have hlog := hdiv.log hdivne
  -- assemble the two terms of `hestonA`
  have hterm3 : HasDerivAt (fun s : ℝ => (2 * κ * θ / ξ ^ 2)
        * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2 * s
            - Real.log (hestonBvDenom κ ξ ρ u s / (2 * hestonGamma κ ξ ρ u))))
      ((2 * κ * θ / ξ ^ 2)
        * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
          - (((hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
                * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u))
              / (2 * hestonGamma κ ξ ρ u))
            / (hestonBvDenom κ ξ ρ u τ / (2 * hestonGamma κ ξ ρ u)))) τ :=
    (hterm2.fun_sub hlog).const_mul (2 * κ * θ / ξ ^ 2)
  have hsum : HasDerivAt (hestonA r κ θ ξ ρ u)
      (r * u + (2 * κ * θ / ξ ^ 2)
        * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
          - (((hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
                * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u))
              / (2 * hestonGamma κ ξ ρ u))
            / (hestonBvDenom κ ξ ρ u τ / (2 * hestonGamma κ ξ ρ u)))) τ :=
    hterm1.fun_add hterm3
  -- the value identity: clean the nested division, then the key lemma
  have hstep1 : (((hestonGamma κ ξ ρ u + κ - ρ * ξ * u)
          * (Real.exp (hestonGamma κ ξ ρ u * τ) * hestonGamma κ ξ ρ u))
        / (2 * hestonGamma κ ξ ρ u))
      / (hestonBvDenom κ ξ ρ u τ / (2 * hestonGamma κ ξ ρ u))
      = (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
          * Real.exp (hestonGamma κ ξ ρ u * τ) / hestonBvDenom κ ξ ρ u τ := by
    field_simp [h2γ, hDne]
  have hmain : (2 * κ * θ / ξ ^ 2)
        * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
          - (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
            * Real.exp (hestonGamma κ ξ ρ u * τ) / hestonBvDenom κ ξ ρ u τ)
      = κ * θ * ((u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1)
          / hestonBvDenom κ ξ ρ u τ) := by
    have hcore : (2 / ξ ^ 2)
          * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
            - (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
              * Real.exp (hestonGamma κ ξ ρ u * τ) / hestonBvDenom κ ξ ρ u τ)
        = (u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1)
            / hestonBvDenom κ ξ ρ u τ := by
      have hL : (2 / ξ ^ 2)
            * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
              - (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
                * Real.exp (hestonGamma κ ξ ρ u * τ) / hestonBvDenom κ ξ ρ u τ)
          = (2 * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
                * hestonBvDenom κ ξ ρ u τ
                - (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
                  * Real.exp (hestonGamma κ ξ ρ u * τ)))
              / (ξ ^ 2 * hestonBvDenom κ ξ ρ u τ) := by
        field_simp [hξ2, hDne]
      rw [hL, div_eq_div_iff (mul_ne_zero hξ2 hDne) hDne]
      linear_combination hestonBvDenom κ ξ ρ u τ * hkey
    calc (2 * κ * θ / ξ ^ 2)
          * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
            - (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
              * Real.exp (hestonGamma κ ξ ρ u * τ) / hestonBvDenom κ ξ ρ u τ)
        = κ * θ * ((2 / ξ ^ 2)
            * ((hestonGamma κ ξ ρ u + κ - ρ * ξ * u) / 2
              - (hestonGamma κ ξ ρ u + κ - ρ * ξ * u) * hestonGamma κ ξ ρ u
                * Real.exp (hestonGamma κ ξ ρ u * τ) / hestonBvDenom κ ξ ρ u τ)) := by
              ring
      _ = κ * θ * ((u ^ 2 - u) * (Real.exp (hestonGamma κ ξ ρ u * τ) - 1)
            / hestonBvDenom κ ξ ρ u τ) := by rw [hcore]
  rw [hstep1, hmain] at hsum
  exact hsum

/-! ### The calendar-time flip (the PDE's time direction) -/

/-- **Calendar-time `Bv`-flow.** `B(t) = b̂(T − t)` solves
`B' = u/2 − u²/2 + (κ − ρξu)B − (ξ²/2)B²` — exactly the `hB` hypothesis of
`hestonProfile_pde` (chain rule: `B'(t) = −b̂'(T − t)`). -/
theorem hasDerivAt_hestonBvCalendar (κ ξ ρ u T : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u)
    (hu2 : u < 1) (t : ℝ) :
    HasDerivAt (fun w => hestonBv κ ξ ρ u (T - w))
      (u / 2 - u ^ 2 / 2 + κ * hestonBv κ ξ ρ u (T - t)
        - ρ * ξ * u * hestonBv κ ξ ρ u (T - t)
        - ξ ^ 2 / 2 * hestonBv κ ξ ρ u (T - t) ^ 2) t := by
  have hts : HasDerivAt (fun w : ℝ => T - w) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hval : ((u ^ 2 - u) / 2 + (ρ * ξ * u - κ) * hestonBv κ ξ ρ u (T - t)
      + ξ ^ 2 / 2 * hestonBv κ ξ ρ u (T - t) ^ 2) * (-1)
      = u / 2 - u ^ 2 / 2 + κ * hestonBv κ ξ ρ u (T - t)
        - ρ * ξ * u * hestonBv κ ξ ρ u (T - t)
        - ξ ^ 2 / 2 * hestonBv κ ξ ρ u (T - t) ^ 2 := by
    ring
  have hcomp : HasDerivAt (fun w : ℝ => hestonBv κ ξ ρ u (T - w))
      (((u ^ 2 - u) / 2 + (ρ * ξ * u - κ) * hestonBv κ ξ ρ u (T - t)
        + ξ ^ 2 / 2 * hestonBv κ ξ ρ u (T - t) ^ 2) * (-1)) t :=
    (hasDerivAt_hestonBv κ ξ ρ u (T - t) hξ hu1 hu2).comp t hts
  rw [hval] at hcomp
  exact hcomp

/-- **Calendar-time `A`-flow.** `A(t) = â(T − t)` solves `A' = −r·u − κθ·B(t)` —
exactly the `hA` hypothesis of `hestonProfile_pde`. -/
theorem hasDerivAt_hestonACalendar (r κ θ ξ ρ u T : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u)
    (hu2 : u < 1) (t : ℝ) :
    HasDerivAt (fun w => hestonA r κ θ ξ ρ u (T - w))
      (-(r * u) - κ * θ * hestonBv κ ξ ρ u (T - t)) t := by
  have hts : HasDerivAt (fun w : ℝ => T - w) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hval : (r * u + κ * θ * hestonBv κ ξ ρ u (T - t)) * (-1)
      = -(r * u) - κ * θ * hestonBv κ ξ ρ u (T - t) := by
    ring
  have hcomp : HasDerivAt (fun w : ℝ => hestonA r κ θ ξ ρ u (T - w))
      ((r * u + κ * θ * hestonBv κ ξ ρ u (T - t)) * (-1)) t :=
    (hasDerivAt_hestonA r κ θ ξ ρ u (T - t) hξ hu1 hu2).comp t hts
  rw [hval] at hcomp
  exact hcomp

/-! ### The PDE headline (mirrors `affineBondPrice_solves_pde` / `cirBondPrice_solves_pde`) -/

/-- The **candidate transform profile** `Φ(t, x, v) = e^{A(t) + u·x + B(t)·v}` with
terminal data `Φ(T, x, v) = e^{u·x}` (the real-moment transform
`M(u) = E[e^{u log S_T}]`; the characteristic function is the same Riccati system
at `iu`). The parameters live in the flows `A, B`. -/
noncomputable def hestonProfile (u : ℝ) (A B : ℝ → ℝ) (t x v : ℝ) : ℝ :=
  Real.exp (A t + u * x + B t * v)

/-- Terminal condition: with the transform's terminal data `A(T) = 0`, `B(T) = 0`
the profile expires to the payoff `e^{u·x}`. -/
theorem hestonProfile_terminal (u : ℝ) (A B : ℝ → ℝ) (T x v : ℝ)
    (hAT : A T = 0) (hBT : B T = 0) :
    hestonProfile u A B T x v = Real.exp (u * x) := by
  simp only [hestonProfile, hAT, hBT, zero_mul, add_zero, zero_add]

/-- **The PDE verification (hypothesis version, the `affineBondPrice_solves_pde` mirror).**
For any coefficient flows `A, B` solving the calendar-time Heston Riccati system

`B' = u/2 − u²/2 + (κ − ρξu)B − (ξ²/2)B²`,  `A' = −r·u − κθ·B`,

the transform profile satisfies the **backward pricing equation**

`∂_t Φ + L Φ = 0`,  `L = hestonGenerator r κ θ ξ ρ`,

for every `(t, x, v)` (no `t < T` hypothesis needed — the identity holds
identically; the terminal condition is `hestonProfile_terminal`). Unlike the bond PDEs
of `Models/Rates/AffineTermStructurePDE` there is no discount term on the right: the
funding rate `r` sits inside the drift of `x`, and the payoff `e^{ux}` carries no
discounting. -/
theorem hestonProfile_pde (r κ θ ξ ρ u : ℝ) (A B : ℝ → ℝ)
    (hB : ∀ s, HasDerivAt B (u / 2 - u ^ 2 / 2 + κ * B s - ρ * ξ * u * B s
        - ξ ^ 2 / 2 * B s ^ 2) s)
    (hA : ∀ s, HasDerivAt A (-(r * u) - κ * θ * B s) s)
    (t x v : ℝ) :
    deriv (fun s => hestonProfile u A B s x v) t
      + hestonGenerator r κ θ ξ ρ (hestonProfile u A B t) x v = 0 := by
  -- time derivative: `Φ_t = (A' + B'·v)·Φ`
  have hinner : HasDerivAt (fun s : ℝ => A s + (u * x) + B s * v)
      (-(r * u) - κ * θ * B t
        + (u / 2 - u ^ 2 / 2 + κ * B t - ρ * ξ * u * B t - ξ ^ 2 / 2 * B t ^ 2) * v) t := by
    simpa only [add_zero] using
      ((hA t).fun_add (hasDerivAt_const t (u * x))).fun_add ((hB t).mul_const v)
  have htime : HasDerivAt (fun s : ℝ => hestonProfile u A B s x v)
      (Real.exp (A t + u * x + B t * v)
        * (-(r * u) - κ * θ * B t
          + (u / 2 - u ^ 2 / 2 + κ * B t - ρ * ξ * u * B t - ξ ^ 2 / 2 * B t ^ 2) * v)) t :=
    hinner.exp
  have htime' : deriv (fun s => hestonProfile u A B s x v) t
      = Real.exp (A t + u * x + B t * v)
        * (-(r * u) - κ * θ * B t
          + (u / 2 - u ^ 2 / 2 + κ * B t - ρ * ξ * u * B t - ξ ^ 2 / 2 * B t ^ 2) * v) :=
    htime.deriv
  -- spatial derivatives: the t-frozen profile *is* `expAffine2 (A t) u (B t)`
  have hf : hestonProfile u A B t = expAffine2 (A t) u (B t) := rfl
  rw [htime', hf, hestonGenerator_expAffine2]
  ring

/-- **The PDE verification (explicit version, the `cirBondPrice_solves_pde` mirror).**
The transform profile built from the explicit Möbius flows
`A(t) = â(T − t)`, `B(t) = b̂(T − t)` satisfies `∂_t Φ + L Φ = 0` for every
`(t, x, v)`. Guards: the strip `0 < u < 1`, `ξ ≠ 0`. -/
theorem hestonTransform_pde (r κ θ ξ ρ u T : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u)
    (hu2 : u < 1) (t x v : ℝ) :
    deriv (fun s => hestonProfile u (fun w => hestonA r κ θ ξ ρ u (T - w))
        (fun w => hestonBv κ ξ ρ u (T - w)) s x v) t
      + hestonGenerator r κ θ ξ ρ (hestonProfile u (fun w => hestonA r κ θ ξ ρ u (T - w))
          (fun w => hestonBv κ ξ ρ u (T - w)) t) x v = 0 :=
  hestonProfile_pde r κ θ ξ ρ u (fun w => hestonA r κ θ ξ ρ u (T - w))
    (fun w => hestonBv κ ξ ρ u (T - w))
    (fun s => hasDerivAt_hestonBvCalendar κ ξ ρ u T hξ hu1 hu2 s)
    (fun s => hasDerivAt_hestonACalendar r κ θ ξ ρ u T hξ hu1 hu2 s) t x v

/-- Terminal condition of the explicit transform: `Φ(T, x, v) = e^{u·x}`
(`â(0) = 0`, `b̂(0) = 0`). -/
theorem hestonTransform_terminal (r κ θ ξ ρ u T x v : ℝ) (hξ : ξ ≠ 0) (hu1 : 0 < u)
    (hu2 : u < 1) :
    hestonProfile u (fun w => hestonA r κ θ ξ ρ u (T - w))
        (fun w => hestonBv κ ξ ρ u (T - w)) T x v
      = Real.exp (u * x) :=
  hestonProfile_terminal u _ _ T x v
    (by simpa using hestonA_at_zero r κ θ ξ ρ u (hestonGamma_ne_zero κ ξ ρ u hξ hu1 hu2))
    (by simpa using hestonBv_at_zero κ ξ ρ u)

end MathFin.Heston
