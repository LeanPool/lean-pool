/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Rates.InterestRateSwap
public import LeanPool.MathFin.Models.ModelFree.CarrMadan
public import LeanPool.MathFin.Pricing.Numeraire
public import LeanPool.MathFin.Models.Rates.ConvexitySensitivity
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Convex.Integral

/-!
# The CMS par-rate functional: convexity, the annuity measure, a Jensen gap

A constant-maturity swap leg pays, at the fixing date `T`, the *then-prevailing*
par swap rate — a nonlinear functional of the curve state, discounted through an
annuity that is itself random; the gap between its value and today's par rate is
the **convexity adjustment**. This module formalizes ingredients of that
adjustment on the swap layer of `MathFin/Models/Rates/InterestRateSwap.lean`
(`payerSwapValue` / `parSwapRate` / `annuity`), but not the adjustment itself
(see the scope note below):

* **The par-rate functional.** `cmsCurveRate P₀ δ C x = (P₀ − x)/(δ·(C + x))` —
  the par rate of a curve whose final discount factor is `x`, other factors
  fixed. Two bridges tie it to the swap layer: `annuity_update_eq` (the annuity
  of an updated curve splits into fixed part + new factor) and
  `parSwapRate_update_eq` / `payerSwapValue_update_eq_zero_iff` (the par
  identity of `payerSwapValue_eq_zero_iff` transports verbatim).
* **Convexity in the discount factor.** `cmsCurveRate_convexOn`: on `[0, ∞)`
  the rate is convex given `δ > 0`, `C > 0` and `0 ≤ P₀ + C` — via the
  shifted-inverse engine
  `convexOn_inv_shift` and the `ConvexOn.smul` / `.add_const` / `.congr`
  combination pattern. First and second derivatives are landed explicitly
  (`hasDerivAt_cmsCurveRate`, `hasDerivAt_cmsCurveRate'`):
  `S''(x) = 2(P₀+C)/(δ(C+x)³)`, positive when `P₀ + C > 0`.
* **The annuity measure.** `annuityMeasure`: the change-of-numéraire measure
  with the annuity `A_T` in the numéraire seat against the money market
  `B = 1/D`, `D` the discount factor to the fixing date, random in general
  (`D = e^{−rT}` is the deterministic money market) — an execution of
  `MathFin.changeOfNumeraire`
  (`Pricing/Numeraire.lean`), alongside the stock and the `T`-bond (the
  forward measure of `Pricing/ForwardMeasure.lean`). `annuityMeasure_price`
  proves `A₀·𝔼^{Qᴬ}[S] = 𝔼^Q[D·S·A_T]` — `Qᴬ`-expectations price
  annuity-settled payoffs `S·A_T`; `annuityMeasure_isProbabilityMeasure` proves
  `Qᴬ` is a probability *given the annuity repricing condition*
  `𝔼^Q[D·A_T] = A₀` — that normalization is where the martingale content
  enters, and it is taken as an explicit hypothesis (`Models/Rates/CMSContract.lean` derives it
  from the tower property when the curve is the bond prices of `D`).
* **The headline.** `cmsCurveRate_jensenGap_nonneg`: Jensen under the annuity measure
  (Mathlib's `ConvexOn.map_integral_le`) gives

    `S(x₀) ≤ 𝔼^{Qᴬ}[S(W)]` whenever `𝔼^{Qᴬ}[W] = x₀`,

  for every nonnegative `W` with `W` and `S ∘ W` `Qᴬ`-integrable: the Jensen gap
  of the rate functional is nonnegative (`cmsCurveRate_jensenGap_sub_nonneg` states the
  gap). `Qᴬ` enters only as a probability measure, `W` is not tied to the curve
  `P` that defines `Qᴬ`, and `S(x₀)` is not shown to be today's par rate.
* **The replication seed.** `cmsCurveRate_spanning`: Carr–Madan static
  replication of the rate functional — cash + forward + put strip + call strip
  with weights `S''(K) = 2(P₀+C)/(δ(C+K)³)` (positive when `P₀ + C > 0`, which
  the identity does not assume); `cmsCurveRate_strip_nonneg` turns it into the
  tangent-line inequality: for `P₀ + C ≥ 0` the rate lies above its tangent at
  the reference strike on `[L, U]`.
* **A bond-convexity sign.** `convexityNumerator_nonneg`: the bond convexity
  numerator `convexityNumerator` of `ConvexitySensitivity` is nonnegative when
  `1 + y > 0` and the cash flows are nonnegative. It is a standalone bond fact;
  nothing here connects it to the CMS rate.

Scope: what lands here is the convexity of the rate functional, the annuity measure, the Jensen gap
under it, and the compact-range replication identity. `Models/Rates/CMSContract.lean` prices CMS
contracts under the annuity measure with the curve tied to the bond prices of a stochastic discount
factor, and restates the Jensen gap for the swap rate. The convexity adjustment for a rate paid at a
later date — `𝔼^{T_p}[S_T] − S₀`, which needs the change of measure from `Qᴬ` to the payment-date
forward measure — is not formalized. The spanning is the compact-strike-range version
(`[L, U]` with `L > −C`); the unbounded-window passage (tail analysis) is not here either. The
swap-rate functional is *not* a log payoff, so the seed consumes `carrMadan_spanning` — the shared
core of which `carrMadan_log_spanning` is the log instance (its proof is one instantiation).

## Main definitions

* `cmsCurveRate`: the par swap rate of a curve whose final discount factor is `x`, all other
  discount factors fixed.
* `annuityRandom`: the random annuity `A_T(ω) = δ · ∑_{i ∈ s} P(ω, T_i)` at the fixing date.
* `annuityMeasure`: the annuity measure `Qᴬ`, the change-of-numéraire measure with the annuity
  `A_T` in the numéraire seat.

## Main results

* `parSwapRate_update_eq`, `payerSwapValue_update_eq_zero_iff`: for `n ∈ s`, the par rate of the
  curve with factor `n` replaced by `x` is `cmsCurveRate`; for `δ > 0`, `x > 0` and positive
  factors, the payer swap on that curve has zero value if and only if `K = cmsCurveRate ...`.
* `hasDerivAt_cmsCurveRate`, `cmsCurveRate_convexOn`: for `δ ≠ 0` and `C + x ≠ 0` the rate has
  derivative `−(P₀+C)/(δ(C+x)²)` at `x`; for `δ > 0`, `C > 0` and `0 ≤ P₀ + C` it is convex on
  `[0, ∞)`.
* `annuityMeasure_isProbabilityMeasure`: with positive `D`, `δ`, `A₀` and curve factors, and the
  annuity repricing condition `𝔼^Q[D·A_T] = A₀` as a hypothesis, `Qᴬ` is a probability measure.
* `annuityMeasure_price`: with positive `D`, `δ`, `A₀` and curve factors, and a measurable
  annuity, `A₀·𝔼^{Qᴬ}[S] = 𝔼^Q[D·S·A_T]` (the normalization is not needed for this identity).
* `cmsCurveRate_jensenGap_nonneg`, `cmsCurveRate_jensenGap_sub_nonneg`: under the positivity
  hypotheses, the repricing condition and `δ > 0`, `C > 0`, `0 ≤ P₀ + C`, for any nonnegative `W`
  with `W` and `S ∘ W` `Qᴬ`-integrable and `𝔼^{Qᴬ}[W] = x₀`, `S(x₀) ≤ 𝔼^{Qᴬ}[S(W)]`; `W` is
  not tied to the curve and `S(x₀)` is not shown to be today's par rate.
* `cmsCurveRate_spanning`: for `δ > 0`, `−C < L ≤ κ ≤ U` and `S ∈ [L, U]`, the rate at `S`
  equals its value at `κ`, plus the tangent term, plus put and call strips weighted by
  `2(P₀+C)/(δ(C+K)³)` (Carr–Madan; no sign condition on `P₀ + C`).
* `cmsCurveRate_strip_nonneg`: with `δ > 0` and `0 ≤ P₀ + C`, the rate lies above its tangent at
  `κ` on `[L, U]` (`−C < L ≤ κ ≤ U`).
* `convexityNumerator_nonneg`: for `1 + y > 0` and nonnegative cash flows, the bond convexity
  numerator is nonnegative (a standalone bond fact, not linked to the CMS rate).

## References

* [P. Carr and D. Madan, *Towards a theory of volatility trading*][CarrMadan1998]
* [P. S. Hagan, *Convexity conundrums: pricing CMS swaps, caps, and floors*][Hagan2003]

## Tags

constant maturity swap, convexity adjustment, annuity measure, swap measure, Jensen gap,
par swap rate, Carr–Madan replication, MSC 91G30, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin.CMS

open MeasureTheory Real MathFin

/-! ### 1. The par-rate functional in the discount factor -/

/-- **The CMS curve rate**: the par swap rate of a curve whose final discount
factor is `x`, all other discount factors fixed. The floating leg is `P₀ − x`,
the annuity `δ·(C + x)` with `C` the sum of the remaining discount factors —
mirroring `MathFin.parSwapRate P₀ x (annuity δ P s)` for the curve `P` updated
at the final payment index (`parSwapRate_update_eq` below). -/
noncomputable def cmsCurveRate (P0 δ C x : ℝ) : ℝ := (P0 - x) / (δ * (C + x))

/-- The annuity of an updated curve splits into the fixed part of the schedule
plus the new factor: `annuity δ (update P n x) s = δ·(∑_{i ≠ n} P i + x)`. -/
private theorem annuity_update_eq {ι : Type*} [DecidableEq ι] (δ : ℝ) (P : ι → ℝ)
    (s : Finset ι) {n : ι} (hn : n ∈ s) (x : ℝ) :
    annuity δ (Function.update P n x) s = δ * ((∑ i ∈ s.erase n, P i) + x) := by
  have hsum : ∑ i ∈ s.erase n, Function.update P n x i + Function.update P n x n
      = ∑ i ∈ s, Function.update P n x i := Finset.sum_erase_add s _ hn
  have hrest : ∑ i ∈ s.erase n, Function.update P n x i = ∑ i ∈ s.erase n, P i :=
    Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) x P
  change δ * ∑ i ∈ s, Function.update P n x i = δ * ((∑ i ∈ s.erase n, P i) + x)
  rw [← hsum, hrest, Function.update_self]

/-- **The bridge to the swap layer**: the par rate of the updated curve *is*
the CMS curve rate. -/
theorem parSwapRate_update_eq {ι : Type*} [DecidableEq ι] (P0 δ x : ℝ) (P : ι → ℝ)
    (s : Finset ι) {n : ι} (hn : n ∈ s) :
    parSwapRate P0 (Function.update P n x n)
        (annuity δ (Function.update P n x) s)
      = cmsCurveRate P0 δ (∑ i ∈ s.erase n, P i) x := by
  change (P0 - Function.update P n x n) / (annuity δ (Function.update P n x) s)
      = cmsCurveRate P0 δ (∑ i ∈ s.erase n, P i) x
  rw [Function.update_self, annuity_update_eq δ P s hn x]
  rfl

/-- **The par identity in curve form** — the CMS instantiation of
`payerSwapValue_eq_zero_iff`: the fixed rate zeroing the payer swap over the
updated curve is exactly the CMS curve rate. -/
theorem payerSwapValue_update_eq_zero_iff {ι : Type*} [DecidableEq ι] (P0 δ K x : ℝ)
    (P : ι → ℝ) (s : Finset ι) {n : ι} (hn : n ∈ s) (hδ : 0 < δ) (hx : 0 < x)
    (hP : ∀ i ∈ s, 0 < P i) :
    payerSwapValue P0 (Function.update P n x n) K (annuity δ (Function.update P n x) s) = 0
      ↔ K = cmsCurveRate P0 δ (∑ i ∈ s.erase n, P i) x := by
  have hup : ∀ i ∈ s, 0 < Function.update P n x i := by
    intro i hi
    by_cases hIn : i = n
    · rw [hIn, Function.update_self]; exact hx
    · rw [Function.update_of_ne hIn x P]
      exact hP i hi
  have hA := annuity_pos hδ hup (⟨n, hn⟩ : s.Nonempty)
  rw [payerSwapValue_eq_zero_iff P0 (Function.update P n x n) K hA.ne',
    parSwapRate_update_eq P0 δ x P s hn]

/-! ### 2. Derivatives and convexity of the rate functional -/

/-- Rewritten form (affine-in-inverse): with `a = P₀ + C`,
`S(x) = a/δ · (C + x)⁻¹ − 1/δ` — the one-line reason the rate is convex when
`P₀ + C ≥ 0` and has second derivative `2a/(δ(C+x)³)`. -/
private theorem cmsCurveRate_eq (P0 δ C x : ℝ) (hx : C + x ≠ 0) (hδ : δ ≠ 0) :
    cmsCurveRate P0 δ C x = (P0 + C) / δ * (C + x)⁻¹ - 1 / δ := by
  rw [cmsCurveRate]
  field_simp
  ring

/-- **First derivative**: `S'(x) = −(P₀ + C)/(δ(C + x)²)`. -/
theorem hasDerivAt_cmsCurveRate (P0 δ C x : ℝ) (hx : C + x ≠ 0) (hδ : δ ≠ 0) :
    HasDerivAt (cmsCurveRate P0 δ C) (-(P0 + C) / (δ * (C + x) ^ 2)) x := by
  have hf : HasDerivAt (fun y : ℝ ↦ P0 - y) (-1 : ℝ) x :=
    HasDerivAt.const_sub P0 (hasDerivAt_id x)
  have hd : HasDerivAt (fun y : ℝ ↦ δ * (y + C)) (δ * 1) x :=
    HasDerivAt.const_mul δ ((hasDerivAt_id x).add_const C)
  have hdx : δ * (x + C) ≠ 0 := by
    refine mul_ne_zero hδ ?_
    rw [add_comm]
    exact hx
  have hdiv : HasDerivAt (fun y : ℝ ↦ (P0 - y) / (δ * (y + C)))
      (((-1 : ℝ) * (δ * (x + C)) - (P0 - x) * (δ * 1)) / (δ * (x + C)) ^ 2) x :=
    HasDerivAt.fun_div hf hd hdx
  rw [show cmsCurveRate P0 δ C = fun y : ℝ ↦ (P0 - y) / (δ * (y + C)) from by
      funext y
      change (P0 - y) / (δ * (C + y)) = (P0 - y) / (δ * (y + C))
      rw [add_comm C y],
    show (-(P0 + C) / (δ * (C + x) ^ 2))
      = (((-1 : ℝ) * (δ * (x + C)) - (P0 - x) * (δ * 1)) / (δ * (x + C)) ^ 2) from by
      rw [div_eq_div_iff (mul_ne_zero hδ (pow_ne_zero 2 hx))
        (pow_ne_zero 2 (mul_ne_zero hδ (by rw [add_comm]; exact hx)))]
      ring]
  exact hdiv

/-- **Second derivative**: `S''(x) = 2(P₀ + C)/(δ(C + x)³)` — positive where
`δ > 0`, `C + x > 0` and `P₀ + C > 0`. -/
theorem hasDerivAt_cmsCurveRate' (P0 δ C t : ℝ) (ht : C + t ≠ 0) (hδ : δ ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -(P0 + C) / (δ * (C + y) ^ 2))
      (2 * (P0 + C) / (δ * (C + t) ^ 3)) t := by
  -- work in the `(y + C)` convention, then convert at the end
  have hu : HasDerivAt (fun y : ℝ ↦ y + C) (1 : ℝ) t := (hasDerivAt_id t).add_const C
  have htc : t + C ≠ 0 := by rw [add_comm]; exact ht
  have hinv : HasDerivAt (fun y : ℝ ↦ (y + C)⁻¹) (-((t + C) ^ 2)⁻¹ * 1) t :=
    (hasDerivAt_inv htc).comp t hu
  have hpow : HasDerivAt (fun y : ℝ ↦ (y + C)⁻¹ * (y + C)⁻¹)
      (-((t + C) ^ 2)⁻¹ * 1 * (t + C)⁻¹ + (t + C)⁻¹ * (-((t + C) ^ 2)⁻¹ * 1)) t :=
    hinv.mul hinv
  have hres := hpow.const_mul (-(P0 + C) / δ)
  rw [show (fun y : ℝ ↦ (-(P0 + C) / δ) * ((y + C)⁻¹ * (y + C)⁻¹))
        = fun y : ℝ ↦ -(P0 + C) / (δ * (y + C) ^ 2) from by
          funext y; field_simp,
      show ((-(P0 + C) / δ) * (-((t + C) ^ 2)⁻¹ * 1 * (t + C)⁻¹
            + (t + C)⁻¹ * (-((t + C) ^ 2)⁻¹ * 1)))
        = 2 * (P0 + C) / (δ * (t + C) ^ 3) from by
        field_simp [mul_inv, inv_pow]
        ring,
      show (fun y : ℝ ↦ -(P0 + C) / (δ * (y + C) ^ 2))
        = fun y : ℝ ↦ -(P0 + C) / (δ * (C + y) ^ 2) from by funext y; ring,
      show (2 * (P0 + C) / (δ * (t + C) ^ 3)) = 2 * (P0 + C) / (δ * (C + t) ^ 3) from by
        rw [add_comm t C]] at hres
  exact hres

/-- Differentiability of the rate functional on the nonnegative half-line —
there the denominator stays `≥ C > 0`. -/
private theorem differentiableOn_cmsCurveRate (P0 δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    DifferentiableOn ℝ (cmsCurveRate P0 δ C) (Set.Ici 0) :=
  fun x hx ↦ ((hasDerivAt_cmsCurveRate P0 δ C x
    (ne_of_gt (show (0 : ℝ) < C + x by linarith [Set.mem_Ici.1 hx]))
        hδ.ne').differentiableAt).differentiableWithinAt

/-- Continuity on the nonnegative half-line — the regularity Jensen consumes. -/
private theorem continuousOn_cmsCurveRate (P0 δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ContinuousOn (cmsCurveRate P0 δ C) (Set.Ici 0) :=
  (differentiableOn_cmsCurveRate P0 δ C hδ hC).continuousOn

/-- **Convexity of the shifted inverse** `x ↦ (C + x)⁻¹` on the nonnegative
half-line — the convexity engine behind the CMS rate's convexity. The two-point
inequality `(u(C+x)+v(C+y))⁻¹ ≤ u(C+x)⁻¹ + v(C+y)⁻¹` is the AM–GM identity
`(ua+vb)(u/a+v/b) − 1 = uv(a−b)²/(ab) ≥ 0` for `a, b > 0`, `u + v = 1`. -/
theorem convexOn_inv_shift (C : ℝ) (hC : 0 < C) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ (C + x)⁻¹) := by
  refine ⟨convex_Ici 0, fun x hx y hy u v hu hv huv ↦ ?_⟩
  change (C + (u * x + v * y))⁻¹ ≤ u * (C + x)⁻¹ + v * (C + y)⁻¹
  have hx0 : (0 : ℝ) ≤ x := Set.mem_Ici.1 hx
  have hy0 : (0 : ℝ) ≤ y := Set.mem_Ici.1 hy
  have hxa : 0 < C + x := by linarith
  have hya : 0 < C + y := by linarith
  have hxu : 0 ≤ u * x := mul_nonneg hu hx0
  have hxv : 0 ≤ v * y := mul_nonneg hv hy0
  have hcomb : C + (u * x + v * y) = u * (C + x) + v * (C + y) := by
    have hCmul : u * C + v * C = C := by linear_combination C * huv
    linarith
  rw [hcomb]
  have hA : 0 < u * (C + x) + v * (C + y) := by rw [← hcomb]; linarith
  have hkey2 : (C + x) * (C + y)
      ≤ (u * (C + x) + v * (C + y)) * (u * (C + y) + v * (C + x)) := by
    have h1 : 0 ≤ u * v * (x - y) ^ 2 := mul_nonneg (mul_nonneg hu hv) (sq_nonneg _)
    have h2 : 0 ≤ (C + x) * (C + y) * ((u + v) ^ 2 - 1) := by rw [huv]; simp
    -- certificate: RHS − LHS = uv(x−y)² + (C+x)(C+y)·((u+v)² − 1), an identity
    nlinarith [h1, h2]
  have hkey : 1 ≤ (u * (C + x)⁻¹ + v * (C + y)⁻¹) * (u * (C + x) + v * (C + y)) := by
    field_simp
    nlinarith
  -- last step: `A⁻¹ ≤ B ↔ 1 ≤ B * A`, avoiding the generic-lemma instance mismatch
  rw [inv_eq_one_div, div_le_iff₀ hA]
  exact hkey

/-- **The CMS rate is convex in the discount factor on the nonnegative
half-line**. Hypotheses: `δ > 0` (daycount),
`C > 0` (the rate functional is defined on the whole half-line) and `P₀ + C ≥ 0`
(the convexity coefficient `S'' = 2(P₀+C)/(δ(C+x)³)` has the right sign;
economically `P₀` and every remaining discount factor are positive, so this is
free). -/
theorem cmsCurveRate_convexOn (P0 δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hPC : 0 ≤ P0 + C) :
    ConvexOn ℝ (Set.Ici (0 : ℝ)) (cmsCurveRate P0 δ C) := by
  have hcoef : (0 : ℝ) ≤ (P0 + C) / δ := div_nonneg hPC hδ.le
  refine (ConvexOn.add_const ((convexOn_inv_shift C hC).smul hcoef) (-1 / δ)).congr ?_
  intro x hx
  have hxne : C + x ≠ 0 :=
    ne_of_gt (show (0 : ℝ) < C + x by linarith [Set.mem_Ici.1 hx])
  simp only [Pi.add_apply, smul_eq_mul]
  rw [cmsCurveRate_eq P0 δ C x hxne hδ.ne']
  ring

/-! ### 3. The annuity measure -/

section Annuity

variable {Ω ι : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The random annuity at the fixing date: `A_T(ω) = δ · ∑_{i ∈ s} P(ω, T_i)` —
the PVBP of the underlying swap along the curve state. -/
noncomputable def annuityRandom (δ : ℝ) (P : Ω → ι → ℝ) (s : Finset ι) : Ω → ℝ :=
  fun ω ↦ annuity δ (P ω) s

omit [MeasurableSpace Ω] in
/-- The annuity is strictly positive along every curve state with positive
discount factors. -/
private theorem annuityRandom_pos {δ : ℝ} (hδ : 0 < δ) {P : Ω → ι → ℝ} {s : Finset ι}
    (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i) (ω : Ω) :
    0 < annuityRandom δ P s ω :=
  annuity_pos hδ (fun i hi ↦ hP ω i hi) hs

/-- **The annuity measure** `Qᴬ`: the change-of-numéraire measure with the
annuity `A_T` in the numéraire seat against the money market `B_T = 1/D`, `D` the (random)
discount factor to the fixing date — an execution of `MathFin.changeOfNumeraire`, alongside the
stock and the `T`-bond (the forward measure of `Pricing/ForwardMeasure.lean`).
Density: `dQᴬ/dQ = A_T·D/A₀`. A deterministic money market `e^{rT}` is `D = e^{−rT}`. -/
noncomputable def annuityMeasure (Q : Measure Ω) (D : Ω → ℝ) (δ : ℝ) (P : Ω → ι → ℝ)
    (s : Finset ι) (A0 : ℝ) : Measure Ω :=
  numeraireMeasure Q (fun ω ↦ (D ω)⁻¹) (annuityRandom δ P s) 1 A0

/-- **The annuity measure is a probability measure** under the annuity-repricing
condition `𝔼^Q[D·A_T] = A₀` — the numéraire engine's normalization
`𝔼^Q[N_T/B_T] = N₀/B₀` read with `N = A`, `B = 1/D` the money market. This hypothesis
is where the martingale content of the CMS construction enters; it is taken
explicitly. -/
theorem annuityMeasure_isProbabilityMeasure {Q : Measure Ω} (D : Ω → ℝ) (δ : ℝ)
    (P : Ω → ι → ℝ) (s : Finset ι) (A0 : ℝ) (hD : ∀ ω, 0 < D ω) (hδ : 0 < δ)
    (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i) (hA0 : 0 < A0)
    (hint : Integrable (fun ω ↦ annuityRandom δ P s ω * D ω) Q)
    (hrepr : ∫ ω, annuityRandom δ P s ω * D ω ∂Q = A0) :
    IsProbabilityMeasure (annuityMeasure Q D δ P s A0) := by
  have hpos : ∀ ω, 0 < annuityRandom δ P s ω := fun ω ↦ annuityRandom_pos hδ hs hP ω
  have hdiv : (fun ω : Ω ↦ annuityRandom δ P s ω / (D ω)⁻¹)
      = fun ω ↦ annuityRandom δ P s ω * D ω := funext fun ω ↦ div_inv_eq_mul _ _
  exact numeraireMeasure_isProbabilityMeasure hpos (fun ω ↦ inv_pos.2 (hD ω)) one_pos hA0
    (by rw [hdiv]; exact hint) (by rw [hdiv, hrepr]; simp)

/-- **The annuity-measure pricing identity** — the annuity in the numéraire seat.
For any `S`,

  `A₀ · 𝔼^{Qᴬ}[S] = 𝔼^Q[D · S · A_T]`,

an execution of `changeOfNumeraire`: `Qᴬ`-expectations price the annuity-settled
payoff `S·A_T`. (A claim paying `S` itself at `T` would be priced through
`S/A_T`; the random `A_T` stays on the `Q` side.) -/
theorem annuityMeasure_price {Q : Measure Ω} (D : Ω → ℝ) (δ : ℝ) (P : Ω → ι → ℝ)
    (s : Finset ι) (A0 : ℝ) (S : Ω → ℝ) (hD : ∀ ω, 0 < D ω) (hDm : Measurable D)
    (hδ : 0 < δ) (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i) (hA0 : 0 < A0)
    (hAmeas : Measurable (annuityRandom δ P s)) :
    A0 * ∫ ω, S ω ∂(annuityMeasure Q D δ P s A0)
      = ∫ ω, D ω * (S ω * annuityRandom δ P s ω) ∂Q := by
  have hpos : ∀ ω, 0 < annuityRandom δ P s ω := fun ω ↦ annuityRandom_pos hδ hs hP ω
  have h := changeOfNumeraire (Q := Q) (BT := fun ω ↦ (D ω)⁻¹)
    (NT := annuityRandom δ P s) (B0 := (1 : ℝ)) (N0 := A0)
    (fun ω ↦ S ω * annuityRandom δ P s ω) hAmeas
    hDm.inv hpos (fun ω ↦ inv_pos.2 (hD ω)) (by norm_num) hA0
  have hcongr : ∀ ω : Ω, annuityRandom δ P s ω ≠ 0 →
      S ω * annuityRandom δ P s ω / annuityRandom δ P s ω = S ω := by
    intro ω hY
    simp [hY]
  rw [integral_congr_ae (ae_of_all _ fun ω ↦ hcongr ω (ne_of_gt (hpos ω)))] at h
  have h2 : 1 * ∫ ω, S ω * annuityRandom δ P s ω / (D ω)⁻¹ ∂Q
      = ∫ ω, D ω * (S ω * annuityRandom δ P s ω) ∂Q := by
    rw [one_mul]
    exact integral_congr_ae (ae_of_all _ fun ω ↦ by
      change S ω * annuityRandom δ P s ω / (D ω)⁻¹ = D ω * (S ω * annuityRandom δ P s ω)
      rw [div_inv_eq_mul, mul_comm])
  rw [← h2]
  exact h

/-! ### 4. The headline: the Jensen gap under the annuity measure -/

-- the Jensen application carries heavy higher-order unification
/-- **The Jensen gap of the CMS rate functional under `Qᴬ`** (the headline). Let
`S = cmsCurveRate P₀ δ C`, with `P₀` and `C` deterministic; it is convex on
`[0, ∞)`. Every nonnegative `W` with `W` and `S ∘ W` integrable under the annuity
measure `Qᴬ` of the previous section satisfies `S(𝔼^{Qᴬ}[W]) ≤ 𝔼^{Qᴬ}[S(W)]`;
`hfwd` only names `x₀ = 𝔼^{Qᴬ}[W]`. `Qᴬ` is a probability measure by `hrepr` and
is used only as one; `W` is not linked to the curve `P` that defines `Qᴬ`, and no
martingale property is assumed. This is not the CMS convexity adjustment
`𝔼^{T_p}[S_T] − S₀`. -/
theorem cmsCurveRate_jensenGap_nonneg {Q : Measure Ω} (D : Ω → ℝ) (δ P0 C A0 x₀ : ℝ)
    (P : Ω → ι → ℝ) (s : Finset ι) (W : Ω → ℝ) (hD : ∀ ω, 0 < D ω) (hδ : 0 < δ) (hC : 0 < C)
    (hPC : 0 ≤ P0 + C) (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i)
    (hA0 : 0 < A0)
    (hint : Integrable (fun ω ↦ annuityRandom δ P s ω * D ω) Q)
    (hrepr : ∫ ω, annuityRandom δ P s ω * D ω ∂Q = A0)
    (hWpos : ∀ ω, 0 ≤ W ω)
    (hWint : Integrable W (annuityMeasure Q D δ P s A0))
    (hSint : Integrable (fun ω ↦ cmsCurveRate P0 δ C (W ω))
      (annuityMeasure Q D δ P s A0))
    (hfwd : ∫ ω, W ω ∂(annuityMeasure Q D δ P s A0) = x₀) :
    cmsCurveRate P0 δ C x₀
      ≤ ∫ ω, cmsCurveRate P0 δ C (W ω) ∂(annuityMeasure Q D δ P s A0) := by
  have hprob := annuityMeasure_isProbabilityMeasure D δ P s A0 hD hδ hs hP hA0 hint hrepr
  have hfs : ∀ᵐ ω ∂(annuityMeasure Q D δ P s A0), W ω ∈ Set.Ici (0 : ℝ) :=
    ae_of_all _ fun ω ↦ Set.mem_Ici.2 (hWpos ω)
  have hj := ConvexOn.map_integral_le (f := W) (g := cmsCurveRate P0 δ C)
    (s := Set.Ici (0 : ℝ)) (cmsCurveRate_convexOn P0 δ C hδ hC hPC)
    (continuousOn_cmsCurveRate P0 δ C hδ hC) isClosed_Ici hfs hWint hSint
  rwa [hfwd] at hj

/-- The Jensen gap itself: `𝔼^{Qᴬ}[S(W)] − S(𝔼^{Qᴬ}[W]) ≥ 0`. -/
theorem cmsCurveRate_jensenGap_sub_nonneg {Q : Measure Ω} (D : Ω → ℝ) (δ P0 C A0 x₀ : ℝ)
    (P : Ω → ι → ℝ) (s : Finset ι) (W : Ω → ℝ) (hD : ∀ ω, 0 < D ω) (hδ : 0 < δ) (hC : 0 < C)
    (hPC : 0 ≤ P0 + C) (hs : s.Nonempty) (hP : ∀ ω i, i ∈ s → 0 < P ω i)
    (hA0 : 0 < A0)
    (hint : Integrable (fun ω ↦ annuityRandom δ P s ω * D ω) Q)
    (hrepr : ∫ ω, annuityRandom δ P s ω * D ω ∂Q = A0)
    (hWpos : ∀ ω, 0 ≤ W ω)
    (hWint : Integrable W (annuityMeasure Q D δ P s A0))
    (hSint : Integrable (fun ω ↦ cmsCurveRate P0 δ C (W ω))
      (annuityMeasure Q D δ P s A0))
    (hfwd : ∫ ω, W ω ∂(annuityMeasure Q D δ P s A0) = x₀) :
    0 ≤ ∫ ω, cmsCurveRate P0 δ C (W ω) ∂(annuityMeasure Q D δ P s A0)
      - cmsCurveRate P0 δ C x₀ :=
  sub_nonneg.2 (cmsCurveRate_jensenGap_nonneg D δ P0 C A0 x₀ P s W hD hδ hC hPC hs hP hA0 hint
    hrepr hWpos hWint hSint hfwd)

end Annuity

/-! ### 5. The replication seed: Carr–Madan spanning of the rate functional -/

-- the Carr–Madan instantiation carries heavy higher-order unification
/-- **The replication seed**: the CMS rate functional spanned as cash + forward
+ static OTM option strips on the discount factor (Carr–Madan, compact strike
range `[L, U]` with `L > −C`). The strip weights are
`S''(K) = 2(P₀+C)/(δ(C+K)³)`, positive when `P₀ + C > 0` (not assumed here). The
swap-rate functional is not a log payoff, so this consumes
`carrMadan_spanning`, the shared core of which `carrMadan_log_spanning` is the
log instance. The unbounded-window limit (tail analysis) is outside the present
scope. -/
theorem cmsCurveRate_spanning (P0 δ C : ℝ) (hδ : 0 < δ)
    {L U κ S : ℝ} (hL : -C < L) (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U) :
    cmsCurveRate P0 δ C S = cmsCurveRate P0 δ C κ
      + (-(P0 + C) / (δ * (C + κ) ^ 2)) * (S - κ)
      + (∫ K in L..κ, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (K - S) 0)
      + (∫ K in κ..U, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (S - K) 0) := by
  have hCK : ∀ K ∈ Set.Icc L U, 0 < C + K := by
    intro K hK
    have h1 : -C < K := by have := hK.1; linarith
    linarith
  exact carrMadan_spanning (f := cmsCurveRate P0 δ C)
    (f' := fun t ↦ -(P0 + C) / (δ * (C + t) ^ 2))
    (f'' := fun K ↦ 2 * (P0 + C) / (δ * (C + K) ^ 3)) hLκ hκU hS
    (fun t ht ↦ hasDerivAt_cmsCurveRate P0 δ C t (ne_of_gt (hCK t ht)) hδ.ne')
    (fun t ht ↦ hasDerivAt_cmsCurveRate' P0 δ C t (ne_of_gt (hCK t ht)) hδ.ne')
    (show ContinuousOn (fun K : ℝ ↦ 2 * (P0 + C) / (δ * (C + K) ^ 3)) (Set.Icc L U) from
      ContinuousOn.div continuousOn_const
        (show ContinuousOn (fun K : ℝ ↦ δ * (C + K) ^ 3) (Set.Icc L U) from
          (Continuous.mul continuous_const
            ((continuous_const.add continuous_id).pow 3)).continuousOn)
        fun K hK ↦ mul_ne_zero hδ.ne' (pow_ne_zero 3 (ne_of_gt (hCK K hK))))

/-- **The tangent-line inequality**: on `[L, U]` the CMS rate lies above its
tangent at `κ`, and the excess is exactly the option strips — nonnegative because
`S'' ≥ 0` (from `P₀ + C ≥ 0`). -/
theorem cmsCurveRate_strip_nonneg (P0 δ C : ℝ) (hδ : 0 < δ) (hPC : 0 ≤ P0 + C)
    {L U κ S : ℝ} (hL : -C < L) (hLκ : L ≤ κ) (hκU : κ ≤ U) (hS : S ∈ Set.Icc L U) :
    0 ≤ cmsCurveRate P0 δ C S - cmsCurveRate P0 δ C κ
        - (-(P0 + C) / (δ * (C + κ) ^ 2)) * (S - κ) := by
  have hspan := cmsCurveRate_spanning P0 δ C hδ hL hLκ hκU hS
  have hCKpos : ∀ K ∈ Set.Icc L U, 0 < C + K := by
    intro K hK
    have h1 : -C < K := by have := hK.1; linarith
    linarith
  have hput : 0 ≤ ∫ K in L..κ, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (K - S) 0 :=
    intervalIntegral.integral_nonneg hLκ fun K hK ↦
      mul_nonneg
        (div_nonneg (mul_nonneg two_pos.le hPC)
          (mul_nonneg hδ.le (pow_nonneg (le_of_lt (hCKpos K
            ⟨hK.1, hK.2.trans hκU⟩)) 3)))
        (le_max_right (K - S) (0 : ℝ))
  have hcall : 0 ≤ ∫ K in κ..U, (2 * (P0 + C) / (δ * (C + K) ^ 3)) * max (S - K) 0 :=
    intervalIntegral.integral_nonneg hκU fun K hK ↦
      mul_nonneg
        (div_nonneg (mul_nonneg two_pos.le hPC)
          (mul_nonneg hδ.le (pow_nonneg (le_of_lt (hCKpos K
            ⟨hLκ.trans hK.1, hK.2⟩)) 3)))
        (le_max_right (S - K) (0 : ℝ))
  linarith

/-! ### 6. A bond-convexity sign -/

/-- **The bond convexity is nonnegative**: each cashflow contributes
`t_i(t_i+1)·c_i/(1+y)^{t_i+2} ≥ 0` for `y > −100%` and nonnegative coupons.
This is the sign of the `P''` exhibited by
`bondPriceDisc_secondDeriv_eq_convexity_times_price`; nothing here connects it
to the CMS rate. -/
theorem convexityNumerator_nonneg {ι : Type*} (s : Finset ι) (t : ι → ℕ) (c : ι → ℝ)
    {y : ℝ} (hy : 0 < 1 + y) (hc : ∀ i ∈ s, 0 ≤ c i) :
    0 ≤ convexityNumerator s t c y := by
  refine Finset.sum_nonneg fun i hi ↦ ?_
  exact div_nonneg
    (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ (t i : ℝ) from Nat.cast_nonneg (α := ℝ) (t i))
      (by linarith [Nat.cast_nonneg (α := ℝ) (t i)])) (hc i hi))
    (pow_nonneg hy.le (t i + 2))

end MathFin.CMS
