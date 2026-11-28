/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.ImpliedVolatility

/-!
# Newton–Raphson: local quadratic convergence

`ImpliedVolatility.lean` records the Newton step `σ ↦ σ − f(σ)/f'(σ)` and its
fixed-point-at-root identity. This file proves the genuine numerical-analysis
content: **local quadratic convergence**.

The hypotheses are the classical ones, phrased through the repo's
`HasDerivAt` idiom (no `ContDiff`/`iteratedDeriv` machinery): on a closed
interval `I = [r − δ, r + δ]` around a root `r`,

* `f` has pointwise derivative `f'` on `I`,
* `f'` is `L`-Lipschitz on `I` (the honest substitute for a second-derivative
  bound — `C²` implies it, but Lipschitz is exactly what the proof consumes),
* `|f'| ≥ m > 0` on `I` (the root is simple).

**One step is quadratic, at the sharp constant**
(`newtonStep_quadratic_error`):

  `|x⁺ − r| ≤ (L/(2m))·(x − r)²`,   `x⁺ := newtonStep f f' x`.

The proof shows *why* Newton is quadratic: the next error is the Taylor
remainder of `f` at `x`, evaluated at the root, divided by `f' x`. The
remainder is the **integral of the derivative deviation** along the segment:
for the linearization-subtracted auxiliary `g(w) = f(w) − f'(x)·w` the FTC
gives `g(x) − g(r) = ∫_r^x (f'(t) − f'(x)) dt`, and the Lipschitz bound
`|f'(t) − f'(x)| ≤ L·|t − x|` is *linear* in the distance to `x`, so it
integrates to `(L/2)·(x − r)²` — the classical Newton–Kantorovich constant.
(A uniform mean-value bound would cost a factor `2`.) No second derivative
is ever mentioned.

**Iterating converges** (`newtonSeq_tendsto_root`): inside the basin
`|x₀ − r| ≤ δ` with `L·δ ≤ m`, the quadratic bound gives the invariant
`|xₙ₊₁ − r| ≤ ½|xₙ − r|`, hence `|xₙ − r| ≤ (½)ⁿ·|x₀ − r| → 0`
(`newtonSeq_error_le_geometric`), and `xₙ → r`.

In the implied-volatility application, `f(σ) = bsV(σ) − C_obs` has
`f' = vega > 0` (`bsV_vega_pos`), so `m` is a positive vega lower bound on the
bracketing interval and the simple-root hypothesis is automatic.

## Main definitions

* `newtonSeq`: the Newton–Raphson iterates, `x₀` and then `x_{n+1} = newtonStep f f' xₙ`.

## Main results

* `newtonStep_quadratic_error`: one-step quadratic error bound `(L/(2m))·e²`.
* `newtonSeq_error_le_geometric`: geometric error decay in the basin.
* `newtonSeq_tendsto_root`: convergence `xₙ → r`.

## Tags

Newton–Raphson, quadratic convergence, implied volatility solver, root finding, numerical analysis,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open Filter Topology

/-- The **Newton–Raphson iterates**: `x₀`, then `x_{n+1} = newtonStep f f' xₙ`. -/
noncomputable def newtonSeq (f f' : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | n + 1 => newtonStep f f' (newtonSeq f f' x₀ n)

variable {f f' : ℝ → ℝ} {r δ m L x₀ : ℝ}

/-- **One Newton step is quadratic, at the sharp constant**: if `r` is a root,
`f'` is the pointwise derivative of `f` on `I = [r − δ, r + δ]`, `f'` is
`L`-Lipschitz on `I`, and `|f'| ≥ m > 0` on `I`, then for `x ∈ I`

  `|newtonStep f f' x − r| ≤ (L/(2m)) · (x − r)²`.

The next error is the Taylor remainder over `f' x`, computed in **integral
form** via the FTC for the linearization-subtracted auxiliary
`w ↦ f w − f' x · w`: its derivative `f' t − f' x` is Lipschitz-bounded by
`L·|t − x|` — *linear* in the distance to `x` — which integrates along
`[r, x]` to the sharp `(L/2)·(x − r)²`; `|f' x| ≥ m` divides it out. -/
theorem newtonStep_quadratic_error
    (hroot : f r = 0) (hm0 : 0 < m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (f' y) y)
    (hlip : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ w ∈ Set.Icc (r - δ) (r + δ),
      |f' y - f' w| ≤ L * |y - w|)
    (hm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |f' y|)
    {x : ℝ} (hx : x ∈ Set.Icc (r - δ) (r + δ)) :
    |newtonStep f f' x - r| ≤ L / (2 * m) * (x - r) ^ 2 := by
  have hδ : 0 ≤ δ := by
    have h1 := hx.1; have h2 := hx.2; linarith
  have hr : r ∈ Set.Icc (r - δ) (r + δ) := ⟨by linarith, by linarith⟩
  have hf'x_pos : 0 < |f' x| := lt_of_lt_of_le hm0 (hm x hx)
  have hf'x_ne : f' x ≠ 0 := abs_pos.1 hf'x_pos
  -- FTC for the linearization-subtracted auxiliary g(w) = f w − f' x · w:
  --   g x − g r = ∫_r^x (f' t − f' x) dt
  have hsub : Set.uIcc r x ⊆ Set.Icc (r - δ) (r + δ) := Set.uIcc_subset_Icc hr hx
  have hg : ∀ t ∈ Set.uIcc r x,
      HasDerivAt (fun w ↦ f w - f' x * w) (f' t - f' x) t := fun t ht ↦
    (hd t (hsub ht)).sub (by simpa using (hasDerivAt_id t).const_mul (f' x))
  have hcontI : ContinuousOn (fun t ↦ f' t - f' x) (Set.Icc (r - δ) (r + δ)) := by
    have hlipOn : LipschitzOnWith (Real.toNNReal L) f' (Set.Icc (r - δ) (r + δ)) :=
      lipschitzOnWith_iff_dist_le_mul.2 fun y hy w hw ↦ by
        rw [Real.dist_eq, Real.dist_eq]
        simpa [Real.coe_toNNReal L hL] using hlip y hy w hw
    exact hlipOn.continuousOn.sub continuousOn_const
  have hftc : ∫ t in r..x, (f' t - f' x)
      = (f x - f' x * x) - (f r - f' x * r) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hg
      ((hcontI.mono hsub).intervalIntegrable)
  -- the linear Lipschitz bound integrates to the sharp (L/2)·(x − r)²
  have h_num : |f' x * (x - r) - f x| ≤ L / 2 * (x - r) ^ 2 := by
    have h_eq : f' x * (x - r) - f x
        = -((f x - f' x * x) - (f r - f' x * r)) := by
      rw [hroot]; ring
    rw [h_eq, abs_neg, ← hftc]
    rcases le_total r x with hrx | hxr
    · have hb : ∀ t ∈ Set.Icc r x, |f' t - f' x| ≤ L * (x - t) := fun t ht ↦ by
        have h := hlip t (hsub (by rw [Set.uIcc_of_le hrx]; exact ht)) x hx
        rwa [abs_sub_comm t x,
          abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ x - t)] at h
      calc |∫ t in r..x, (f' t - f' x)|
          ≤ ∫ t in r..x, |f' t - f' x| :=
            intervalIntegral.abs_integral_le_integral_abs hrx
        _ ≤ ∫ t in r..x, L * (x - t) :=
            intervalIntegral.integral_mono_on hrx
              (hcontI.mono hsub).abs.intervalIntegrable
              ((continuous_const.mul
                (continuous_const.sub continuous_id)).intervalIntegrable r x)
              hb
        _ = L / 2 * (x - r) ^ 2 := by
            -- second FTC: the dominating integrand has explicit primitive
            -- s ↦ L·(x·s − s²/2)
            have hP : ∀ t ∈ Set.uIcc r x,
                HasDerivAt (fun s ↦ L * (x * s - s ^ 2 / 2)) (L * (x - t)) t := by
              intro t _
              have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
                have h := (hasDerivAt_pow 2 t).div_const 2
                norm_num at h
                exact h
              have h1 : HasDerivAt (fun s : ℝ ↦ x * s) x t := by
                simpa using (hasDerivAt_id t).const_mul x
              simpa using (h1.sub h2).const_mul L
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP
              ((continuous_const.mul
                (continuous_const.sub continuous_id)).intervalIntegrable r x)]
            ring
    · have hb : ∀ t ∈ Set.Icc x r, |f' t - f' x| ≤ L * (t - x) := fun t ht ↦ by
        have h := hlip t
          (Set.uIcc_subset_Icc hx hr (by rw [Set.uIcc_of_le hxr]; exact ht)) x hx
        rwa [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - x)] at h
      rw [intervalIntegral.integral_symm, abs_neg]
      calc |∫ t in x..r, (f' t - f' x)|
          ≤ ∫ t in x..r, |f' t - f' x| :=
            intervalIntegral.abs_integral_le_integral_abs hxr
        _ ≤ ∫ t in x..r, L * (t - x) :=
            intervalIntegral.integral_mono_on hxr
              (hcontI.mono (Set.uIcc_subset_Icc hx hr)).abs.intervalIntegrable
              ((continuous_const.mul
                (continuous_id.sub continuous_const)).intervalIntegrable x r)
              hb
        _ = L / 2 * (x - r) ^ 2 := by
            -- second FTC: the dominating integrand has explicit primitive
            -- s ↦ L·(s²/2 − x·s)
            have hP : ∀ t ∈ Set.uIcc x r,
                HasDerivAt (fun s ↦ L * (s ^ 2 / 2 - x * s)) (L * (t - x)) t := by
              intro t _
              have h2 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
                have h := (hasDerivAt_pow 2 t).div_const 2
                norm_num at h
                exact h
              have h1 : HasDerivAt (fun s : ℝ ↦ x * s) x t := by
                simpa using (hasDerivAt_id t).const_mul x
              simpa using (h2.sub h1).const_mul L
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP
              ((continuous_const.mul
                (continuous_id.sub continuous_const)).intervalIntegrable x r)]
            ring
  -- error–times–derivative identity: (x⁺ − r)·f' x = f' x·(x − r) − f x
  have h_prod : (newtonStep f f' x - r) * f' x = f' x * (x - r) - f x := by
    unfold newtonStep
    field_simp
    ring
  rw [show L / (2 * m) * (x - r) ^ 2 = L / 2 * (x - r) ^ 2 / m by ring,
    le_div_iff₀ hm0]
  calc |newtonStep f f' x - r| * m
      ≤ |newtonStep f f' x - r| * |f' x| :=
        mul_le_mul_of_nonneg_left (hm x hx) (abs_nonneg _)
    _ = |(newtonStep f f' x - r) * f' x| := (abs_mul _ _).symm
    _ = |f' x * (x - r) - f x| := by rw [h_prod]
    _ ≤ L / 2 * (x - r) ^ 2 := h_num

/-- **Geometric error decay in the Newton basin**: if additionally
`|x₀ − r| ≤ δ` and `L·δ ≤ m`, then every iterate stays in the interval and

  `|xₙ − r| ≤ (½)ⁿ · |x₀ − r|`.

The sharp quadratic bound `(L/(2m))·e²` turns into the halving `e/2` as soon
as `e ≤ δ ≤ m/L`, and halving preserves the basin — the induction
invariant. -/
theorem newtonSeq_error_le_geometric
    (hroot : f r = 0) (hm0 : 0 < m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (f' y) y)
    (hlip : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ w ∈ Set.Icc (r - δ) (r + δ),
      |f' y - f' w| ≤ L * |y - w|)
    (hm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |f' y|)
    (hx₀ : |x₀ - r| ≤ δ) (hbasin : L * δ ≤ m) :
    ∀ n, |newtonSeq f f' x₀ n - r| ≤ (1 / 2) ^ n * |x₀ - r| := by
  intro n
  induction n with
  | zero => simp [newtonSeq]
  | succ n ih =>
    have h_en_le_δ : |newtonSeq f f' x₀ n - r| ≤ δ := by
      refine ih.trans (le_trans ?_ hx₀)
      calc (1 / 2 : ℝ) ^ n * |x₀ - r|
          ≤ 1 * |x₀ - r| :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ (by norm_num) (by norm_num)) (abs_nonneg _)
        _ = |x₀ - r| := one_mul _
    have h_mem : newtonSeq f f' x₀ n ∈ Set.Icc (r - δ) (r + δ) := by
      have h := abs_le.1 h_en_le_δ
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have h_step := newtonStep_quadratic_error hroot hm0 hL hd hlip hm h_mem
    have h_coeff : L / (2 * m) * δ ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * m)]
      linarith
    have h_half : L / (2 * m) * (newtonSeq f f' x₀ n - r) ^ 2
        ≤ 1 / 2 * |newtonSeq f f' x₀ n - r| := by
      calc L / (2 * m) * (newtonSeq f f' x₀ n - r) ^ 2
          = L / (2 * m) * |newtonSeq f f' x₀ n - r| * |newtonSeq f f' x₀ n - r| := by
            rw [mul_assoc, abs_mul_abs_self, ← pow_two]
        _ ≤ L / (2 * m) * δ * |newtonSeq f f' x₀ n - r| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_en_le_δ
                (div_nonneg hL (by positivity : (0:ℝ) ≤ 2 * m)))
              (abs_nonneg _)
        _ ≤ 1 / 2 * |newtonSeq f f' x₀ n - r| :=
            mul_le_mul_of_nonneg_right h_coeff (abs_nonneg _)
    change |newtonStep f f' (newtonSeq f f' x₀ n) - r| ≤ (1 / 2) ^ (n + 1) * |x₀ - r|
    calc |newtonStep f f' (newtonSeq f f' x₀ n) - r|
        ≤ L / (2 * m) * (newtonSeq f f' x₀ n - r) ^ 2 := h_step
      _ ≤ 1 / 2 * |newtonSeq f f' x₀ n - r| := h_half
      _ ≤ 1 / 2 * ((1 / 2) ^ n * |x₀ - r|) := by linarith [ih]
      _ = (1 / 2) ^ (n + 1) * |x₀ - r| := by ring

/-- **Newton–Raphson converges** in the basin: under the quadratic-error
hypotheses with `|x₀ − r| ≤ δ` and `L·δ ≤ m`, the iterates tend to the root.
Squeeze of the geometric decay `(½)ⁿ·|x₀ − r| → 0`. -/
theorem newtonSeq_tendsto_root
    (hroot : f r = 0) (hm0 : 0 < m) (hL : 0 ≤ L)
    (hd : ∀ y ∈ Set.Icc (r - δ) (r + δ), HasDerivAt f (f' y) y)
    (hlip : ∀ y ∈ Set.Icc (r - δ) (r + δ), ∀ w ∈ Set.Icc (r - δ) (r + δ),
      |f' y - f' w| ≤ L * |y - w|)
    (hm : ∀ y ∈ Set.Icc (r - δ) (r + δ), m ≤ |f' y|)
    (hx₀ : |x₀ - r| ≤ δ) (hbasin : L * δ ≤ m) :
    Tendsto (newtonSeq f f' x₀) atTop (𝓝 r) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h_geo : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * |x₀ - r|) atTop (𝓝 0) := by
    have h_pow : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h_pow.mul_const |x₀ - r|
  refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) h_geo
  rw [Real.dist_eq]
  exact newtonSeq_error_le_geometric hroot hm0 hL hd hlip hm hx₀ hbasin n

end MathFin
