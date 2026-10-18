/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic


/-!
# Weighted power means with a negative exponent

The analytic engine of Carroll and Kimball (1996). For CRRA utility `u' c = c ^ (-γ)` the
first-order condition of a consumption–saving problem reads

  `c = (β R) ^ (-1/γ) · (∑ π z' · c' z' ^ (-γ)) ^ (-1/γ)`,

so the consumption chosen against a given stock of end-of-period assets is a positive multiple
of the weighted power mean, with exponent `-γ`, of next period's consumptions. Carroll and
Kimball's induction therefore needs exactly one fact: **a power mean with a negative exponent
is concave and nondecreasing**, so it carries concavity of next period's consumption functions
to concavity of this period's.

## The proof

`powerMean w p` is positively homogeneous of degree one, so concavity is the statement that the
set `{x > 0 : powerMean w p x ≥ 1}` is convex. With `p < 0` that set is `{x > 0 : ∑ w x ^ p ≤ 1}`
— a sublevel set of `∑ w x ^ p`, which is convex because `t ↦ t ^ p` is. So the whole thing comes
down to convexity of a single real function of one variable, and the scaling is bookkeeping.

`convexOn_rpow_of_neg` supplies that one function: Mathlib has `x ^ p` convex for `1 ≤ p` and
concave for `0 < p < 1`, but not the negative case, and it is proved here from concavity of
`log` and convexity of `exp`.

Kimball's risk-tolerance aggregation theorem is the differential form of the same fact. This is
the integrated form, and it needs no derivatives.
-/

@[expose] public section

open Set Finset

namespace LeanEconomics

/-! ### `x ^ p` is convex for a negative exponent -/

/-- **A negative power is convex on the positive half-line.** `x ^ p = exp (p log x)`: `log` is
concave, multiplying by `p < 0` flips that to convex, and `exp` is convex and increasing. -/
theorem convexOn_rpow_of_neg {p : ℝ} (hp : p < 0) :
    ConvexOn ℝ (Ioi (0 : ℝ)) fun x : ℝ => x ^ p := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have hm : (0 : ℝ) < a * x + b * y := by
    rcases eq_or_lt_of_le ha with h | h
    · have hb1 : b = 1 := by linarith
      rw [← h, hb1]; simpa using hy0
    · nlinarith
  -- concavity of `log`
  have hlog : a * Real.log x + b * Real.log y ≤ Real.log (a * x + b * y) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 hx hy ha hb hab
    simpa using this
  -- multiplying by `p < 0` reverses it
  have hstep : p * Real.log (a * x + b * y) ≤ a * (p * Real.log x) + b * (p * Real.log y) := by
    nlinarith
  calc (a * x + b * y) ^ p
      = Real.exp (p * Real.log (a * x + b * y)) := by
        rw [Real.rpow_def_of_pos hm]; ring_nf
    _ ≤ Real.exp (a * (p * Real.log x) + b * (p * Real.log y)) := Real.exp_le_exp.mpr hstep
    _ ≤ a * Real.exp (p * Real.log x) + b * Real.exp (p * Real.log y) := by
        simpa using convexOn_exp.2 (mem_univ (p * Real.log x)) (mem_univ (p * Real.log y)) ha hb hab
    _ = a • x ^ p + b • y ^ p := by
        rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hy0]
        simp only [smul_eq_mul]
        ring_nf

/-! ### The power mean -/

variable {ι : Type*} [Fintype ι]

/-- A convex combination of two positive numbers is positive. -/
theorem pos_of_convex_comb {u v θ φ : ℝ} (hu : 0 < u) (hv : 0 < v) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (hθφ : θ + φ = 1) : 0 < θ * u + φ * v := by
  rcases eq_or_lt_of_le hθ with h | h
  · have hφ1 : φ = 1 := by linarith
    rw [← h, hφ1]; simpa using hv
  · nlinarith

/-- The weighted power mean of `x` with exponent `p`. -/
noncomputable def powerMean (w : ι → ℝ) (p : ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, w i * x i ^ p) ^ (1 / p)

variable {w : ι → ℝ} {p : ℝ} {x y : ι → ℝ}

theorem sum_rpow_pos (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    0 < ∑ i, w i * x i ^ p := by
  obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ Finset.univ, 0 < w i := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    have hzero : ∑ i, w i = 0 :=
      Finset.sum_eq_zero fun i hi => le_antisymm (h i hi) (hw i)
    rw [hw1] at hzero
    norm_num at hzero
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (hx i).le _))
    ⟨i₀, Finset.mem_univ _, mul_pos hi₀ (Real.rpow_pos_of_pos (hx i₀) _)⟩

theorem powerMean_pos (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    0 < powerMean w p x :=
  Real.rpow_pos_of_pos (sum_rpow_pos hw hw1 hx) _

/-- The mean raised back to the exponent recovers the weighted sum. -/
theorem powerMean_rpow (hp : p ≠ 0) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) : powerMean w p x ^ p = ∑ i, w i * x i ^ p := by
  have hS : 0 < ∑ i, w i * x i ^ p := sum_rpow_pos hw hw1 hx
  simp only [powerMean]
  rw [← Real.rpow_mul hS.le, one_div_mul_cancel hp, Real.rpow_one]

/-- **The power mean is positively homogeneous of degree one.** -/
theorem powerMean_smul (hp : p ≠ 0) {c : ℝ} (hc : 0 < c) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 < x i) :
    powerMean w p (fun i => c * x i) = c * powerMean w p x := by
  have hS : 0 < ∑ i, w i * x i ^ p := sum_rpow_pos hw hw1 hx
  have hrw : ∑ i, w i * (c * x i) ^ p = c ^ p * ∑ i, w i * x i ^ p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow hc.le (hx i).le]; ring
  simp only [powerMean, hrw]
  rw [Real.mul_rpow (Real.rpow_nonneg hc.le _) hS.le, ← Real.rpow_mul hc.le,
    mul_one_div_cancel hp, Real.rpow_one]

/-- **Normalising by the mean makes the weighted sum exactly one.** This is the statement that
the level set `{powerMean = 1}` is where the scaling argument lands. -/
theorem sum_rpow_div_powerMean (hp : p ≠ 0) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) : ∑ i, w i * (x i / powerMean w p x) ^ p = 1 := by
  have hS : 0 < ∑ i, w i * x i ^ p := sum_rpow_pos hw hw1 hx
  have hM : 0 < powerMean w p x := powerMean_pos hw hw1 hx
  have hrw : ∀ i, w i * (x i / powerMean w p x) ^ p
      = (powerMean w p x ^ p)⁻¹ * (w i * x i ^ p) := by
    intro i
    rw [Real.div_rpow (hx i).le hM.le]; ring
  rw [Finset.sum_congr rfl fun i _ => hrw i, ← Finset.mul_sum, powerMean_rpow hp hw hw1 hx]
  exact inv_mul_cancel₀ hS.ne'

/-- **A power mean with a negative exponent is nondecreasing.** -/
theorem powerMean_mono (hp : p < 0) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hxy : ∀ i, x i ≤ y i) :
    powerMean w p x ≤ powerMean w p y := by
  have h1 : ∑ i, w i * y i ^ p ≤ ∑ i, w i * x i ^ p :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (hx i) (hxy i) hp.le) (hw i)
  exact Real.rpow_le_rpow_of_nonpos (sum_rpow_pos hw hw1 hy) h1
    (le_of_lt (div_neg_of_pos_of_neg one_pos hp))

/-- **The gradient sum of a power mean is at most `M / min x`.** The quantity
`∑ w x^{-γ-1}`, which is what a common shift costs when propagated through a power mean, is bounded
termwise by `∑ w x^{-γ} / min x`.

This is worth recording as a WARNING rather than a tool. Normalised, it says the gradient sum
`A = ∑ w (x/M)^{-γ-1}` is at most `M / min x` — and `M / min x` is exactly the multiplier that
bounding the expectation by its smallest term produces. Measured in the overlapping-generations
life cycle, `A` runs from `1.04` to `1.19` while `M / min x` runs from `4.7` to `5.9`, so this bound
discards the entire advantage of keeping the certainty equivalent. A usable bound on `A` has to see
the WEIGHTS — the far states carry little probability — and not merely the support. -/
theorem sum_mul_rpow_pred_le {γ xmin : ℝ} (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 < x i)
    (hmin : 0 < xmin) (hle : ∀ i, xmin ≤ x i) :
    ∑ i, w i * x i ^ (-γ - 1) ≤ (∑ i, w i * x i ^ (-γ)) / xmin := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : x i ^ (-γ - 1) = x i ^ (-γ) * (x i)⁻¹ := by
    rw [show (-γ - 1 : ℝ) = (-γ) + (-1) from by ring, Real.rpow_add (hx i), Real.rpow_neg_one]
  have hinv : (x i)⁻¹ ≤ xmin⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hmin (hle i)
  have hnn : 0 ≤ w i * x i ^ (-γ) := mul_nonneg (hw i) (Real.rpow_nonneg (hx i).le _)
  calc w i * x i ^ (-γ - 1) = (w i * x i ^ (-γ)) * (x i)⁻¹ := by rw [hsplit]; ring
    _ ≤ (w i * x i ^ (-γ)) * xmin⁻¹ := mul_le_mul_of_nonneg_left hinv hnn
    _ = w i * x i ^ (-γ) / xmin := by rw [div_eq_mul_inv]

/-- **The gradient sum is one plus the variance of the risk tilt.** Write `u i = (x i / M) ^ (-γ)`
for the tilt. By the definition of the power mean its weighted mean is exactly one, and then the
gradient sum `∑ w u ^ (1 + 1/γ)` is, at `γ = 1` where the exponent is exactly two, one plus the
weighted variance of `u`.

This is the bound the minimum cannot give. `sum_mul_rpow_pred_le` sees only the support of `x` and
returns `M / min x`, measured at `4.7` to `5.9`; the variance sees the WEIGHTS, and is measured at
`0.041`. For `γ > 1` the exponent `1 + 1/γ` falls below two and Lyapunov's inequality gives
`∑ w u ^ (1+1/γ) ≤ (1 + Var)^{(γ+1)/(2γ)}`, which is an identity at `γ = 1` and loses accuracy
above it: measured `1.076` against a true `1.050` at `γ = 1.5`, and `1.26` against `1.08` at
`γ = 3`, against an allowance of about `1.06` throughout. So this route closes at logarithmic
utility and not above (`WriteUps/WriteUpOLG/numerics/lyap.m`). -/
theorem sum_mul_sq_eq_one_add_variance {w u : ι → ℝ} (hw1 : ∑ i, w i = 1)
    (hu : ∑ i, w i * u i = 1) :
    ∑ i, w i * u i ^ 2 = 1 + ∑ i, w i * (u i - 1) ^ 2 := by
  have hexp : ∀ i, w i * (u i - 1) ^ 2 = w i * u i ^ 2 - 2 * (w i * u i) + w i := by
    intro i; ring
  rw [Finset.sum_congr rfl fun i _ => hexp i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hu, hw1]
  ring

/-- **The sharp moment bound.** For weights summing to one, `u ≥ 0` with `∑ w u = 1` and
`1 < p < 2`, `∑ w u^p ≤ (∑ w u²)^(p-1)`. It is Jensen for the concave `x ↦ x^(p-1)` under the
tilted weights `w u`, which sum to one by hypothesis, and it is attained by the two-point law on
`{0, ∑ w u²}`. With `p = 1 + 1/γ` it bounds the gradient sum of the two-rate chain by
`(1 + Var)^(1/γ)`, against Lyapunov's `(1 + Var)^((γ+1)/(2γ))`. -/
theorem sum_mul_rpow_le_rpow_sum_mul_sq {w u : ι → ℝ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) (hmean : ∑ i, w i * u i = 1) :
    ∑ i, w i * u i ^ p ≤ (∑ i, w i * u i ^ 2) ^ (p - 1) := by
  have hp0 : p - 1 ≠ 0 := sub_ne_zero.2 (ne_of_gt hp1)
  have hq : (1 : ℝ) ≤ 1 / (p - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h := Real.arith_mean_le_rpow_mean Finset.univ (fun i => w i * u i)
    (fun i => u i ^ (p - 1)) (fun i _ => mul_nonneg (hw i) (hu i)) hmean
    (fun i _ => Real.rpow_nonneg (hu i) _) hq
  have hL : ∀ i, w i * u i * u i ^ (p - 1) = w i * u i ^ p := by
    intro i
    have e : u i ^ p = u i ^ (1 + (p - 1)) := by congr 1; ring
    rw [e, Real.rpow_add' (hu i) (by linarith : (1 : ℝ) + (p - 1) ≠ 0), Real.rpow_one]
    ring
  have hR : ∀ i, w i * u i * (u i ^ (p - 1)) ^ (1 / (p - 1)) = w i * u i ^ 2 := by
    intro i
    rw [one_div, Real.rpow_rpow_inv (hu i) hp0]
    ring
  simp only [hL, hR, one_div_one_div] at h
  exact h

/-- **A power mean with a negative exponent is concave.**

Homogeneity turns concavity into the convexity of `{x > 0 : ∑ w x ^ p ≤ 1}`, and that is a
sublevel set of a convex function. This is Kimball's risk-tolerance aggregation in integrated
form: no derivative appears anywhere. -/
theorem powerMean_concave (hp : p < 0) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    {θ φ : ℝ} (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hθφ : θ + φ = 1) :
    θ * powerMean w p x + φ * powerMean w p y
      ≤ powerMean w p (fun i => θ * x i + φ * y i) := by
  have hp0 : p ≠ 0 := ne_of_lt hp
  have hA : 0 < powerMean w p x := powerMean_pos hw hw1 hx
  have hB : 0 < powerMean w p y := powerMean_pos hw hw1 hy
  set A := powerMean w p x with hAdef
  set B := powerMean w p y with hBdef
  set d : ℝ := θ * A + φ * B with hddef
  have hd : 0 < d := pos_of_convex_comb hA hB hθ hφ hθφ
  have hz : ∀ i, 0 < θ * x i + φ * y i := fun i => pos_of_convex_comb (hx i) (hy i) hθ hφ hθφ
  -- the weights that split the normalised combination
  set μ : ℝ := θ * A / d with hμdef
  set ν : ℝ := φ * B / d with hνdef
  have hμ : 0 ≤ μ := by rw [hμdef]; positivity
  have hν : 0 ≤ ν := by rw [hνdef]; positivity
  have hμν : μ + ν = 1 := by
    have hsum : μ + ν = (θ * A + φ * B) / d := by rw [hμdef, hνdef]; ring
    rw [hsum, ← hddef, div_self hd.ne']
  -- convexity of `t ^ p`, one coordinate at a time
  have hpt : ∀ i, ((θ * x i + φ * y i) / d) ^ p ≤ μ * (x i / A) ^ p + ν * (y i / B) ^ p := by
    intro i
    have hkey : (θ * x i + φ * y i) / d = μ * (x i / A) + ν * (y i / B) := by
      rw [hμdef, hνdef]; field_simp
    rw [hkey]
    have := (convexOn_rpow_of_neg hp).2 (show x i / A ∈ Ioi (0 : ℝ) by
        simpa using div_pos (hx i) hA)
      (show y i / B ∈ Ioi (0 : ℝ) by simpa using div_pos (hy i) hB) hμ hν hμν
    simpa using this
  -- summing, the normalised combination sits inside the unit sublevel set
  have hsum : ∑ i, w i * ((θ * x i + φ * y i) / d) ^ p ≤ 1 := by
    calc ∑ i, w i * ((θ * x i + φ * y i) / d) ^ p
        ≤ ∑ i, w i * (μ * (x i / A) ^ p + ν * (y i / B) ^ p) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw i)
      _ = μ * (∑ i, w i * (x i / A) ^ p) + ν * ∑ i, w i * (y i / B) ^ p := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := by
          rw [hAdef, hBdef, sum_rpow_div_powerMean hp0 hw hw1 hx,
            sum_rpow_div_powerMean hp0 hw hw1 hy, mul_one, mul_one, hμν]
  -- and the mean of a vector in that set is at least one
  have hT : 0 < ∑ i, w i * ((θ * x i + φ * y i) / d) ^ p :=
    sum_rpow_pos hw hw1 fun i => div_pos (hz i) hd
  have hge : (1 : ℝ) ≤ powerMean w p (fun i => (θ * x i + φ * y i) / d) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hsum
      (le_of_lt (div_neg_of_pos_of_neg one_pos hp))
  -- rescale
  have hscale : powerMean w p (fun i => θ * x i + φ * y i)
      = d * powerMean w p (fun i => (θ * x i + φ * y i) / d) := by
    rw [← powerMean_smul hp0 hd hw hw1 fun i => div_pos (hz i) hd]
    congr 1
    funext i
    field_simp
  rw [hscale]
  calc d = d * 1 := (mul_one d).symm
    _ ≤ d * powerMean w p (fun i => (θ * x i + φ * y i) / d) :=
        mul_le_mul_of_nonneg_left hge hd.le

/-- **The Carroll–Kimball step.** A negative power mean of concave positive functions is
concave: concavity of next period's consumption functions carries to the consumption chosen
against a given stock of end-of-period assets. -/
theorem concaveOn_powerMean_comp {D : Set ℝ} (hD : Convex ℝ D) (hp : p < 0)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {f : ι → ℝ → ℝ}
    (hpos : ∀ i, ∀ a ∈ D, 0 < f i a) (hconc : ∀ i, ConcaveOn ℝ D (f i)) :
    ConcaveOn ℝ D (fun a => powerMean w p (fun i => f i a)) := by
  refine ⟨hD, fun a ha b hb θ φ hθ hφ hθφ => ?_⟩
  have hm : θ • a + φ • b ∈ D := hD ha hb hθ hφ hθφ
  have hstep : ∀ i, θ * f i a + φ * f i b ≤ f i (θ • a + φ • b) := by
    intro i
    have := (hconc i).2 ha hb hθ hφ hθφ
    simpa using this
  have hmid : ∀ i, 0 < θ * f i a + φ * f i b := fun i =>
    pos_of_convex_comb (hpos i a ha) (hpos i b hb) hθ hφ hθφ
  calc θ • powerMean w p (fun i => f i a) + φ • powerMean w p (fun i => f i b)
      = θ * powerMean w p (fun i => f i a) + φ * powerMean w p (fun i => f i b) := by
        simp only [smul_eq_mul]
    _ ≤ powerMean w p (fun i => θ * f i a + φ * f i b) :=
        powerMean_concave hp hw hw1 (fun i => hpos i a ha) (fun i => hpos i b hb) hθ hφ hθφ
    _ ≤ powerMean w p (fun i => f i (θ • a + φ • b)) :=
        powerMean_mono hp hw hw1 hmid (fun i => hpos i _ hm) hstep

/-- **And nondecreasing**, which the endogenous-gridpoint transfer also needs. -/
theorem monotoneOn_powerMean_comp {D : Set ℝ} (hp : p < 0)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {f : ι → ℝ → ℝ}
    (hpos : ∀ i, ∀ a ∈ D, 0 < f i a) (hmono : ∀ i, MonotoneOn (f i) D) :
    MonotoneOn (fun a => powerMean w p (fun i => f i a)) D := fun a ha b hb hab =>
  powerMean_mono hp hw hw1 (fun i => hpos i a ha) (fun i => hpos i b hb)
    fun i => hmono i ha hb hab

end LeanEconomics
