/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.PDE
public import LeanPool.MathFin.Models.BlackScholes.GreekSigns
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Spot-direction convexity of the Black–Scholes call

`StrikeConvexity.lean` packages convexity-in-`K` at four scales; this file
is its spot-direction dual at the two scales that make sense for `S`:

1. **Payoff level**, `S ↦ max(S − K, 0)`: the positive part of an affine
   function is convex.
2. **Continuous price level**, `S ↦ bsV K r σ S τ`: strictly convex on `(0, ∞)`
   by the second-derivative test — gamma is positive
   (`hasDerivAt_deriv_bsV_S` + `strictConvexOn_of_deriv2_pos'`).

Financially: pricing preserves the convexity of the payoff. Gamma-positivity
(`bsV_gamma_pos`) is the infinitesimal face of the same fact, and makes the
convexity strict. The supporting-tangent form below (`bsV_spot_tangent_le`,
slope = delta) is the workhorse for Jensen-type mixture bounds:
`MertonDominance.lean` and `JumpDiffusionMixing.lean` consume it to prove that a
jump-diffusion call dominates the Black–Scholes call, and `JumpImpliedVol.lean`
consumes the strict form (`bsV_spot_tangent_lt`) to make the domination strict.

## Main results

* `convexOn_call_payoff_spot`: `S ↦ max(S − K, 0)` is convex (payoff level).
* `bsV_spot_strictConvexOn`, `bsV_spot_convexOn`: `S ↦ bsV K r σ S τ` is strictly convex, hence
  convex, on `(0, ∞)` (continuous price level).
* `bsV_spot_tangent_lt`, `bsV_spot_tangent_le`: the price lies above its tangent at any
  `S₀ > 0`, with slope delta, `bsV(S₀) + Φ(d₁(S₀))·(s − S₀) ≤ bsV(s)`, strictly away from the
  point of tangency.

## References

* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], §4.5

## Tags

gamma positivity, price convexity in spot, convex payoff, tangent bound, Jensen mixture, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open Set Real ProbabilityTheory

/-- **Call payoff is convex in the spot**: `S ↦ max(S − K, 0)` is the
positive part of an affine function. The spot-direction sibling of
`convexOn_call_payoff`. -/
lemma convexOn_call_payoff_spot (K : ℝ) :
    ConvexOn ℝ Set.univ (fun S : ℝ ↦ max (S - K) 0) := by
  refine ConvexOn.sup ⟨convex_univ, fun a _ b _ s t _ _ hst ↦ ?_⟩
    (convexOn_const (0 : ℝ) convex_univ)
  change s • a + t • b - K ≤ s • (a - K) + t • (b - K)
  simp only [smul_eq_mul]
  have h_kk : s * K + t * K = K := by linear_combination K * hst
  linarith

/-! ## The continuous-price face

The proof is the second-derivative test; the strike side instead integrates the payoff against
the standard normal law (`bsV_strike_convexOn`):

* `hasDerivAt_bsV_S`: `∂_S bsV = Φ(d₁)` (delta) exists at every `S > 0`.
* `hasDerivAt_deriv_bsV_S`: `∂²_S bsV = ϕ(d₁)/(S σ √τ)` (gamma) exists at every
  `S > 0`, and it is positive (`bsV_gamma_pos`). -/

/-- **BS call price is strictly convex in the spot on `(0, ∞)`**: at every `S > 0` the gamma
`∂²_S bsV = ϕ(d₁)/(S σ √τ)` is positive (`bsV_gamma_pos`). -/
theorem bsV_spot_strictConvexOn {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun s ↦ bsV K r σ s τ) :=
  strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
    (fun _ hS ↦ (hasDerivAt_bsV_S hK hσ hS hτ).continuousAt.continuousWithinAt)
    fun _ hS ↦ (bsV_gamma_pos (r := r) hK hσ hS hτ).trans_eq
      (hasDerivAt_deriv_bsV_S hK hσ hS hτ).deriv.symm

/-- **BS call price is convex in the spot on `(0, ∞)`** — the continuous-price face of
S-convexity; the strict form is `bsV_spot_strictConvexOn`. -/
theorem bsV_spot_convexOn {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun s ↦ bsV K r σ s τ) :=
  (bsV_spot_strictConvexOn hK hσ hτ).convexOn

/-- **The price lies strictly above its tangent away from `S₀`**: for `s ≠ S₀`,
`bsV(S₀) + Φ(d₁(S₀))·(s − S₀) < bsV(s)`. Strict convexity (`bsV_spot_strictConvexOn`) plus the
closed-form delta (`hasDerivAt_bsV_S`), through the slope comparison lemmas. -/
theorem bsV_spot_tangent_lt {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hτ : 0 < τ) {S₀ s : ℝ} (hS₀ : 0 < S₀) (hs : 0 < s) (hne : s ≠ S₀) :
    bsV K r σ S₀ τ + Phi (bsd1 S₀ K r σ τ) * (s - S₀) < bsV K r σ s τ := by
  have hconv := bsV_spot_strictConvexOn (K := K) (r := r) (σ := σ) (τ := τ) hK hσ hτ
  have hder := hasDerivAt_bsV_S (K := K) (r := r) (σ := σ) hK hσ hS₀ hτ
  rcases hne.lt_or_gt with hlt | hgt
  · -- to the left of S₀: slope s S₀ < delta.
    have h := hconv.slope_lt_of_hasDerivAt (Set.mem_Ioi.mpr hs) (Set.mem_Ioi.mpr hS₀) hlt hder
    rw [slope_def_field] at h
    have h' := (div_lt_iff₀ (sub_pos.mpr hlt)).mp h
    linarith
  · -- to the right of S₀: delta < slope S₀ s.
    have h := hconv.lt_slope_of_hasDerivAt (Set.mem_Ioi.mpr hS₀) (Set.mem_Ioi.mpr hs) hgt hder
    rw [slope_def_field] at h
    have h' := (lt_div_iff₀ (sub_pos.mpr hgt)).mp h
    linarith

/-- **The price lies above its tangent at any `S₀ > 0`, with slope delta**:
`bsV(S₀) + Φ(d₁(S₀))·(s − S₀) ≤ bsV(s)`, the supporting-hyperplane form of `bsV_spot_convexOn`;
away from `S₀` it is `bsV_spot_tangent_lt`. -/
theorem bsV_spot_tangent_le {K r σ τ : ℝ} (hK : 0 < K) (hσ : 0 < σ)
    (hτ : 0 < τ) {S₀ s : ℝ} (hS₀ : 0 < S₀) (hs : 0 < s) :
    bsV K r σ S₀ τ + Phi (bsd1 S₀ K r σ τ) * (s - S₀) ≤ bsV K r σ s τ := by
  rcases eq_or_ne s S₀ with rfl | hne
  · simp
  · exact (bsV_spot_tangent_lt hK hσ hτ hS₀ hs hne).le

end MathFin
