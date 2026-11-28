/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.CIRRiccati
public import LeanPool.MathFin.Models.Rates.VasicekBondPrice

/-!
# Affine bond prices solve the term-structure PDE

In a one-factor affine short-rate model `dr = κ(θ − r) dt + √(α + β r) dW`, bond prices take
the form `P = exp(A(τ) − B(τ)·r)` in the time to maturity `τ`, with loadings solving the
Riccati system

  `B' = 1 − κB − ½βB²`,   `A' = −κθB + ½αB²`,   `A(0) = B(0) = 0`

(Duffie–Kan; that general statement is not proved here). `affineBondPrice_solves_pde` proves
the step from the Riccati system to the pricing equation: whenever `A` and `B` satisfy the two
equations at `τ`, the function
`u(τ, r) = exp(A(τ) − B(τ)·r)` satisfies, at `(τ, r)`, the term-structure PDE

  `−∂_τ u + κ(θ − r)·∂_r u + ½(α + β r)·∂²_r u − r·u = 0`.

Two models are instances:

* **Cox–Ingersoll–Ross**, `(α, β) = (0, σ²)`: the closed-form loadings `cirBondA`, `cirBondB`
  of `Models/Rates/CIRRiccati.lean` solve their Riccati equations there, so `exp(A − B·r)`
  solves the CIR pricing PDE (`cirBondPrice_solves_pde`). That this closed form equals the
  expectation `𝔼[exp(−∫₀ᵀ r_s ds)]` (Feynman–Kac for the CIR process) is not proved.
* **Vasicek**, `(α, β) = (σ², 0)`: the rate loading `vasicekBondB` solves `B' = 1 − κB`
  (`hasDerivAt_vasicekBondB`), the variance `vasicekBondV` has derivative `B²`
  (`hasDerivAt_vasicekBondV`), so `log vasicekBondA` solves `A' = −κθB + ½σ²B²`
  (`hasDerivAt_log_vasicekBondA`), and `vasicekBondA·exp(−B·r)` solves the Vasicek pricing PDE
  (`vasicekBondPrice_solves_pde`). Here the closed form is the expectation:
  `vasicekBondPrice_affine` (`Models/Rates/VasicekBondPrice.lean`) derives
  `𝔼[exp(−∫₀ᵀ r_s ds)] = vasicekBondA·exp(−B·r₀)` from the Gaussian law of the integrated rate.

At zero volatility the two models coincide, and so do their rate loadings:
`cirBondB κ 0 = vasicekBondB κ` for `κ ≠ 0` (`cirBondB_zero_vol`).

## Main results

* `affineBondPrice_solves_pde` — the Riccati system implies the term-structure PDE.
* `cirBondPrice_solves_pde` — the CIR closed form solves the CIR PDE, for `σ ≠ 0`.
* `hasDerivAt_vasicekBondB`, `hasDerivAt_vasicekBondV`, `hasDerivAt_log_vasicekBondA` — the
  Vasicek loadings solve their Riccati equations, for `κ ≠ 0`.
* `vasicekBondPrice_solves_pde` — the Vasicek affine price solves the Vasicek PDE, for `κ ≠ 0`.
* `cirBondB_zero_vol` — the CIR rate loading at `σ = 0` is the Vasicek rate loading.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  §3.2.3
* [J. C. Cox, J. E. Ingersoll and S. A. Ross, *A theory of the term structure of interest
  rates*][CoxIngersollRoss1985]
* [D. Duffie and R. Kan, *A yield-factor model of interest rates*][DuffieKan1996]
* [O. Vasicek, *An equilibrium characterization of the term structure*][Vasicek1977]

## Tags

term structure PDE, Riccati equation, affine short-rate model, Cox–Ingersoll–Ross, Vasicek model,
bond pricing equation, MSC 91G30, MSC 35K10, JEL E43
-/

@[expose] public section

namespace MathFin

/-! ### The Riccati system implies the pricing PDE -/

/-- **Affine bond prices solve the term-structure PDE** (Duffie–Kan, one factor). If the
loadings satisfy the Riccati equations `A' = −κθB + ½αB²` and `B' = 1 − κB − ½βB²` at `τ`, then
`u(τ, r) = exp(A(τ) − B(τ)·r)` satisfies
`−∂_τ u + κ(θ − r)·∂_r u + ½(α + β r)·∂²_r u − r·u = 0` at `(τ, r)`: the drift `κ(θ − r)` and
the variance `α + βr` of the short rate `dr = κ(θ − r)dt + √(α + βr) dW`. -/
theorem affineBondPrice_solves_pde {κ θ α β : ℝ} {A B : ℝ → ℝ} {τ : ℝ}
    (hA : HasDerivAt A (-(κ * θ) * B τ + α / 2 * B τ ^ 2) τ)
    (hB : HasDerivAt B (1 - κ * B τ - β / 2 * B τ ^ 2) τ) (r : ℝ) :
    -deriv (fun t ↦ Real.exp (A t - B t * r)) τ
      + κ * (θ - r) * deriv (fun x ↦ Real.exp (A τ - B τ * x)) r
      + (α + β * r) / 2 * deriv (deriv fun x ↦ Real.exp (A τ - B τ * x)) r
      - r * Real.exp (A τ - B τ * r) = 0 := by
  have hτ : HasDerivAt (fun t ↦ Real.exp (A t - B t * r))
      (Real.exp (A τ - B τ * r)
        * ((-(κ * θ) * B τ + α / 2 * B τ ^ 2) - (1 - κ * B τ - β / 2 * B τ ^ 2) * r)) τ :=
    (hA.sub (hB.mul_const r)).exp
  have hx (x : ℝ) : HasDerivAt (fun y ↦ Real.exp (A τ - B τ * y))
      (Real.exp (A τ - B τ * x) * -B τ) x :=
    (((hasDerivAt_id' x).const_mul (B τ)).const_sub (A τ)).exp.congr_deriv (by ring)
  have hxx : HasDerivAt (fun y ↦ Real.exp (A τ - B τ * y) * -B τ)
      (Real.exp (A τ - B τ * r) * -B τ * -B τ) r :=
    (hx r).mul_const (-B τ)
  rw [hτ.deriv, (hx r).deriv, show deriv (fun y ↦ Real.exp (A τ - B τ * y))
      = fun y ↦ Real.exp (A τ - B τ * y) * -B τ from funext fun y ↦ (hx y).deriv, hxx.deriv]
  ring

/-! ### Cox–Ingersoll–Ross -/

/-- **The CIR closed form solves the CIR pricing PDE.** For `σ ≠ 0`, the closed-form loadings
`cirBondA`, `cirBondB` make `u(τ, r) = exp(A(τ) − B(τ)·r)` a solution of
`−∂_τ u + κ(θ − r)·∂_r u + ½σ² r·∂²_r u − r·u = 0` (the affine PDE with `(α, β) = (0, σ²)`).
That `u` is the bond price `𝔼[exp(−∫₀ᵀ r_s ds)]` of the CIR process is not proved. -/
theorem cirBondPrice_solves_pde (κ θ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) (τ r : ℝ) :
    -deriv (fun t ↦ Real.exp (cirBondA κ θ σ t - cirBondB κ σ t * r)) τ
      + κ * (θ - r) * deriv (fun x ↦ Real.exp (cirBondA κ θ σ τ - cirBondB κ σ τ * x)) r
      + σ ^ 2 * r / 2 * deriv (deriv fun x ↦ Real.exp (cirBondA κ θ σ τ - cirBondB κ σ τ * x)) r
      - r * Real.exp (cirBondA κ θ σ τ - cirBondB κ σ τ * r) = 0 := by
  have h := affineBondPrice_solves_pde (κ := κ) (θ := θ) (α := 0) (β := σ ^ 2)
    ((hasDerivAt_cirBondA κ θ hσ τ).congr_deriv (by ring))
    (hasDerivAt_cirBondB (by positivity) τ) r
  rwa [show (0 + σ ^ 2 * r) / 2 = σ ^ 2 * r / 2 by ring] at h

/-! ### Vasicek -/

/-- **The Vasicek rate loading solves `B' = 1 − κB`** (the CIR Riccati equation without its
quadratic term), for `κ ≠ 0`: `B(T) = (1 − e^{−κT})/κ` has derivative `e^{−κT}`. -/
theorem hasDerivAt_vasicekBondB {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ) :
    HasDerivAt (vasicekBondB κ) (1 - κ * vasicekBondB κ T) T := by
  have he : HasDerivAt (fun t ↦ Real.exp (-(κ * t))) (Real.exp (-(κ * T)) * -κ) T :=
    ((hasDerivAt_id' T).const_mul κ).neg.exp.congr_deriv (by simp only [Pi.neg_apply, mul_one])
  refine ((he.const_sub 1).div_const κ).congr_deriv ?_
  rw [vasicekBondB]
  field_simp
  ring

/-- **The Vasicek variance has derivative `B²`**: `V' = vasicekBondB²`, for `κ ≠ 0`, where
`V(T) = T/κ² − 2(1 − e^{−κT})/κ³ + (1 − e^{−2κT})/(2κ³)` is `vasicekBondV`. -/
theorem hasDerivAt_vasicekBondV {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ) :
    HasDerivAt (vasicekBondV κ) (vasicekBondB κ T ^ 2) T := by
  have e1 : HasDerivAt (fun t ↦ Real.exp (-(κ * t))) (Real.exp (-(κ * T)) * -κ) T :=
    ((hasDerivAt_id' T).const_mul κ).neg.exp.congr_deriv (by simp only [Pi.neg_apply, mul_one])
  have e2 : HasDerivAt (fun t ↦ Real.exp (-(2 * κ * t))) (Real.exp (-(2 * κ * T)) * -(2 * κ)) T :=
    ((hasDerivAt_id' T).const_mul (2 * κ)).neg.exp.congr_deriv
      (by simp only [Pi.neg_apply, mul_one])
  have hE : Real.exp (-(2 * κ * T)) = Real.exp (-(κ * T)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ((((hasDerivAt_id' T).div_const (κ ^ 2)).sub
    (((e1.const_sub 1).const_mul 2).div_const (κ ^ 3))).add
    ((e2.const_sub 1).div_const (2 * κ ^ 3))).congr_deriv ?_
  rw [vasicekBondB, hE]
  field_simp
  ring

/-- The Vasicek level loading in log form: `log A(T) = −θ(T − B(T)) + σ²V(T)/2`, where
`vasicekBondA` is the exponential of that expression. -/
theorem log_vasicekBondA (θ σ κ T : ℝ) :
    Real.log (vasicekBondA θ σ κ T)
      = -(θ * (T - vasicekBondB κ T)) + σ ^ 2 * vasicekBondV κ T / 2 :=
  Real.log_exp _

/-- **The Vasicek level loading solves `A' = −κθB + ½σ²B²`** (log form), for `κ ≠ 0`: the
CIR level equation with the quadratic term moved from the rate loading to the level loading
(constant variance `σ²` instead of `σ² r`). -/
theorem hasDerivAt_log_vasicekBondA (θ σ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ) :
    HasDerivAt (fun t ↦ Real.log (vasicekBondA θ σ κ t))
      (-(κ * θ) * vasicekBondB κ T + σ ^ 2 / 2 * vasicekBondB κ T ^ 2) T := by
  simp only [log_vasicekBondA]
  exact ((((hasDerivAt_id' T).sub (hasDerivAt_vasicekBondB hκ T)).const_mul θ).neg.add
    (((hasDerivAt_vasicekBondV hκ T).const_mul (σ ^ 2)).div_const 2)).congr_deriv (by ring)

/-- **The Vasicek affine price solves the Vasicek pricing PDE.** For `κ ≠ 0`,
`u(τ, r) = vasicekBondA(τ)·exp(−vasicekBondB(τ)·r)` satisfies
`−∂_τ u + κ(θ − r)·∂_r u + ½σ²·∂²_r u − r·u = 0` (the affine PDE with `(α, β) = (σ², 0)`).
By `vasicekBondPrice_affine`, for `κ > 0` and `τ = T ≥ 0` this `u` is the bond price
`𝔼[exp(−∫₀ᵀ r_s ds)]` of the Vasicek short rate started at `r`. -/
theorem vasicekBondPrice_solves_pde (θ σ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (τ r : ℝ) :
    -deriv (fun t ↦ vasicekBondA θ σ κ t * Real.exp (-(vasicekBondB κ t * r))) τ
      + κ * (θ - r) * deriv (fun x ↦ vasicekBondA θ σ κ τ * Real.exp (-(vasicekBondB κ τ * x))) r
      + σ ^ 2 / 2
        * deriv (deriv fun x ↦ vasicekBondA θ σ κ τ * Real.exp (-(vasicekBondB κ τ * x))) r
      - r * (vasicekBondA θ σ κ τ * Real.exp (-(vasicekBondB κ τ * r))) = 0 := by
  have hfun (t x : ℝ) : vasicekBondA θ σ κ t * Real.exp (-(vasicekBondB κ t * x))
      = Real.exp (Real.log (vasicekBondA θ σ κ t) - vasicekBondB κ t * x) := by
    rw [log_vasicekBondA, vasicekBondA, ← Real.exp_add]
    rfl
  simp only [hfun]
  have h := affineBondPrice_solves_pde (κ := κ) (θ := θ) (α := σ ^ 2) (β := 0)
    (hasDerivAt_log_vasicekBondA θ σ hκ τ)
    ((hasDerivAt_vasicekBondB hκ τ).congr_deriv (by ring)) r
  rwa [show (σ ^ 2 + 0 * r) / 2 = σ ^ 2 / 2 by ring] at h

/-! ### Zero volatility -/

/-- **At zero volatility the CIR rate loading is the Vasicek rate loading**:
`cirBondB κ 0 T = vasicekBondB κ T = (1 − e^{−κT})/κ` for `κ ≠ 0`. Both models reduce to the
deterministic short rate `r' = κ(θ − r)`, and `γ = √(κ²) = |κ|`. -/
theorem cirBondB_zero_vol {κ : ℝ} (hκ : κ ≠ 0) (T : ℝ) : cirBondB κ 0 T = vasicekBondB κ T := by
  have hγ : cirGamma κ 0 = |κ| := by simp [cirGamma, Real.sqrt_sq_eq_abs]
  rcases lt_or_gt_of_ne hκ with hneg | hpos
  · rw [abs_of_neg hneg] at hγ
    have hD : cirDenom κ 0 T = -(2 * κ) := by rw [cirDenom, hγ]; ring
    rw [cirBondB, hD, hγ, vasicekBondB, neg_mul]
    field_simp
    ring
  · rw [abs_of_pos hpos] at hγ
    have hD : cirDenom κ 0 T = 2 * κ * Real.exp (κ * T) := by rw [cirDenom, hγ]; ring
    rw [cirBondB, hD, hγ, vasicekBondB, Real.exp_neg]
    field_simp

end MathFin
