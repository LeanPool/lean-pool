/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Smoothing
public import LeanPool.FunctionSpaces.Analysis.Differences.Differences

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Steklov smoothing on the whole line

For a continuous `f : ℝ → ℂ`, an order `r ∈ ℕ` and a step `δ > 0`, the **Steklov smoothing**
`S_δ f = ∑_{k=1}^r (-1)^(k+1) C(r, k) M_{kδ}^r f` (`Interval.smooth`, defined pointwise on all of
`ℝ` from the Steklov averages `M_η g(x) = η^(-1) ∫_0^η g(x + τ) dτ`) is `r` times continuously
differentiable (`Interval.contDiff_smooth`). On all of `ℝ` it is controlled by the modulus of
smoothness of the line, `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(ℝ)}` (`Rd.modulus volume`):

* `‖f - S_δ f‖_{L_p(ℝ)} ≤ ω_r(f, rδ)_p` for `1 ≤ p < ∞`
  (`Daubechies.eLpNorm_sub_smooth_le_modulus`);
* `‖(S_δ f)^(r)‖_{L_p(ℝ)} ≤ 2^r δ^(-r) ω_r(f, rδ)_p` for `1 ≤ p ≤ ∞`
  (`Daubechies.eLpNorm_iteratedDeriv_smooth_le_modulus`).

The proofs are those of the interval versions `Interval.eLpNorm_sub_smooth_le` and
`Interval.eLpNorm_iteratedDeriv_smooth_le`, with Lebesgue measure on `ℝ` in place of its
restriction to an interval. The difference `f - S_δ f` is `(-1)^r` times the average of
`Δ^r_{v_1 + ⋯ + v_r} f` over `v ∈ [0, δ]^r` (`Interval.sub_smooth_eq`), so Minkowski's inequality
for averages (`Interval.eLpNorm_avgStepIter_le`) bounds it by the differences with steps
`0 ≤ h ≤ rδ`. The derivative is the combination
`(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f`
(`Interval.iteratedDeriv_smooth_eq_sum_smul`), bounded by the derivative bound for any measure
(`Interval.eLpNorm_sum_smoothCoeff_smul_le`) with `‖Δ_h^r f‖_p ≤ ω_r(f, rδ)_p` for `0 ≤ h ≤ rδ`.

At the dyadic step `δ = 1/(N 2^j)`, where `Nδ = 2^(-j)` and `δ^(-N) = N^N 2^(jN)`, the two
bounds read `‖f - S_δ f‖_p ≤ ω_N(f, 2^(-j))_p` and
`‖(S_δ f)^(N)‖_p ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p` (`Daubechies.eLpNorm_sub_smooth_le_dyadic`,
`Daubechies.eLpNorm_iteratedDeriv_smooth_le_dyadic`), and for `f ∈ L_p` both `S_δ f` and
`(S_δ f)^(r)` lie in `L_p` (`Daubechies.memLp_smooth`, `Daubechies.memLp_iteratedDeriv_smooth`).
These are the smoothing steps of Jackson's inequality for the Daubechies projections.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Daubechies

/-! ### The two smoothing estimates on the line -/

/-- **Differences with a nonnegative step are bounded by the modulus**: for `0 ≤ h ≤ t`,
`‖Δ_h^r f‖_{L_p(ℝ)} ≤ ω_r(f, t)_p`, where `ω_r(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^r f‖_{L_p(ℝ)}` is the
modulus of smoothness of the line (`Rd.modulus volume`). -/
theorem eLpNorm_higherDiff_le_modulus_of_nonneg {r : ℕ} {p : ℝ≥0∞} {f : ℝ → ℂ} {h t : ℝ}
    (h0 : 0 ≤ h) (ht : h ≤ t) :
    eLpNorm (Rd.higherDiff r h f) p volume ≤ Rd.modulus volume r p f t :=
  Rd.eLpNorm_higherDiff_le_modulus (by rwa [Real.norm_of_nonneg h0])

/-- **The smoothing is close to `f` on the whole line**: for continuous `f : ℝ → ℂ`, `r ∈ ℕ`,
`δ > 0` and `1 ≤ p < ∞`,
`‖f - S_δ f‖_{L_p(ℝ)} ≤ ω_r(f, rδ)_p`.
Indeed `f - S_δ f = (-1)^r avg_{v ∈ [0, δ]^r} Δ^r_{v_1 + ⋯ + v_r} f` (`Interval.sub_smooth_eq`),
and Minkowski's inequality for averages (`Interval.eLpNorm_avgStepIter_le`, stated for
`p < ∞`) bounds its norm by the supremum of `‖Δ_h^r f‖_{L_p(ℝ)}` over `0 ≤ h ≤ rδ`. -/
theorem eLpNorm_sub_smooth_le_modulus {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => f x - Interval.smooth r δ f x) p volume ≤
      Rd.modulus volume r p f (r * δ) := by
  have heq : (fun x => f x - Interval.smooth r δ f x) = ((-1 : ℂ) ^ r) •
      Interval.avgStepIter r δ (fun h y => Rd.higherDiff r h f y) 0 := by
    funext x
    rw [Interval.sub_smooth_eq hf r hδ.ne' x]
    rfl
  rw [heq, eLpNorm_const_smul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul]
  refine (Interval.eLpNorm_avgStepIter_le (Interval.continuous_higherDiff_uncurry hf r) hδ hp
    hp' volume r 0).trans (iSup₂_le fun h hh => ?_)
  rw [zero_add] at hh
  exact eLpNorm_higherDiff_le_modulus_of_nonneg hh.1 hh.2

/-- **The derivative of order `r` of the smoothing on the whole line**: for continuous
`f : ℝ → ℂ`, `r ∈ ℕ`, `δ > 0` and `1 ≤ p ≤ ∞`,
`‖(S_δ f)^(r)‖_{L_p(ℝ)} ≤ 2^r δ^(-r) ω_r(f, rδ)_p`,
by the triangle inequality for `(S_δ f)^(r) = ∑_{k=1}^r (-1)^(k+1) C(r, k) (kδ)^(-r) Δ_{kδ}^r f`
and `∑_{k=1}^r C(r, k) ≤ 2^r` (`Interval.eLpNorm_sum_smoothCoeff_smul_le` for Lebesgue measure on
`ℝ`). -/
theorem eLpNorm_iteratedDeriv_smooth_le_modulus {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (iteratedDeriv r (Interval.smooth r δ f)) p volume ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * Rd.modulus volume r p f (r * δ) := by
  rw [Interval.iteratedDeriv_smooth_eq_sum_smul hf r δ]
  exact Interval.eLpNorm_sum_smoothCoeff_smul_le (D := fun h => Rd.higherDiff r h f) hδ hp
    fun h h0 hh => eLpNorm_higherDiff_le_modulus_of_nonneg h0 hh

/-! ### The dyadic step `δ = 1/(N 2^j)` -/

/-- **The smoothing at a dyadic scale is close to `f`**: for continuous `f : ℝ → ℂ`, `N ≥ 1`,
`j ∈ ℕ`, `1 ≤ p < ∞` and the step `δ = 1/(N 2^j)`,
`‖f - S_δ f‖_{L_p(ℝ)} ≤ ω_N(f, 2^(-j))_p`.
This is `eLpNorm_sub_smooth_le_modulus` with `r = N`, since `Nδ = 2^(-j)`. -/
theorem eLpNorm_sub_smooth_le_dyadic {f : ℝ → ℂ} (hf : Continuous f) {N : ℕ} (hN : 0 < N)
    (j : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm (fun x => f x - Interval.smooth N (1 / (N * 2 ^ j)) f x) p volume ≤
      Rd.modulus volume N p f (1 / 2 ^ j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < 1 / (N * 2 ^ j) := div_pos one_pos (mul_pos hN' (pow_pos two_pos j))
  have hNδ : (N : ℝ) * (1 / (N * 2 ^ j)) = 1 / 2 ^ j := by field_simp
  have h := eLpNorm_sub_smooth_le_modulus hf N hδ hp hp'
  rwa [hNδ] at h

/-- **The derivative of the smoothing at a dyadic scale**: for continuous `f : ℝ → ℂ`, `N ≥ 1`,
`j ∈ ℕ`, `1 ≤ p ≤ ∞` and the step `δ = 1/(N 2^j)`,
`‖(S_δ f)^(N)‖_{L_p(ℝ)} ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p`.
This is `eLpNorm_iteratedDeriv_smooth_le_modulus` with `r = N`, since `δ^(-N) = N^N 2^(jN)`
and `Nδ = 2^(-j)`. -/
theorem eLpNorm_iteratedDeriv_smooth_le_dyadic {f : ℝ → ℂ} (hf : Continuous f) {N : ℕ}
    (hN : 0 < N) (j : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (iteratedDeriv N (Interval.smooth N (1 / (N * 2 ^ j)) f)) p volume ≤
      2 ^ N * (N : ℝ≥0∞) ^ N * 2 ^ (j * N) * Rd.modulus volume N p f (1 / 2 ^ j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : (0 : ℝ) < 1 / (N * 2 ^ j) := div_pos one_pos (mul_pos hN' (pow_pos two_pos j))
  have hNδ : (N : ℝ) * (1 / (N * 2 ^ j)) = 1 / 2 ^ j := by field_simp
  have hinv : (ENNReal.ofReal (1 / (N * 2 ^ j)))⁻¹ ^ N = (N : ℝ≥0∞) ^ N * 2 ^ (j * N) := by
    rw [← ENNReal.ofReal_inv_of_pos hδ, one_div, inv_inv, ENNReal.ofReal_mul hN'.le,
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, mul_pow,
      ← pow_mul]
  have h := eLpNorm_iteratedDeriv_smooth_le_modulus hf N hδ hp
  rwa [hinv, hNδ, ← mul_assoc] at h

/-! ### `L_p` membership -/

/-- **The smoothing of an `L_p` function lies in `L_p`**: for continuous `f ∈ L_p(ℝ)`, `r ∈ ℕ`,
`δ > 0` and `1 ≤ p < ∞`, also `S_δ f ∈ L_p(ℝ)`, because
`‖f - S_δ f‖_p ≤ ω_r(f, rδ)_p ≤ 2^r ‖f‖_p` (`Rd.modulus_le`). -/
theorem memLp_smooth {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : Continuous f) (hfp : MemLp f p volume)
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    MemLp (Interval.smooth r δ f) p volume := by
  have hsub : MemLp (fun x => f x - Interval.smooth r δ f x) p volume := memLp_iff.2 <|
    calc eLpNorm (fun x => f x - Interval.smooth r δ f x) p volume
        ≤ Rd.modulus volume r p f (r * δ) := eLpNorm_sub_smooth_le_modulus hf r hδ hp hp'
      _ ≤ 2 ^ r * eLpNorm f p volume := Rd.modulus_le hf.aestronglyMeasurable hp r _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) hfp.eLpNorm_lt_top
  have heq : Interval.smooth r δ f = f - fun x => f x - Interval.smooth r δ f x := by
    funext x
    simp
  rw [heq]
  exact hfp.sub hsub

/-- **The derivative of the smoothing of an `L_p` function lies in `L_p`**: for continuous
`f ∈ L_p(ℝ)`, `r ∈ ℕ`, `δ > 0` and `1 ≤ p ≤ ∞`, also `(S_δ f)^(r) ∈ L_p(ℝ)`, because
`‖(S_δ f)^(r)‖_p ≤ 2^r δ^(-r) ω_r(f, rδ)_p ≤ 4^r δ^(-r) ‖f‖_p`. -/
theorem memLp_iteratedDeriv_smooth {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : Continuous f)
    (hfp : MemLp f p volume) (r : ℕ) {δ : ℝ} (hδ : 0 < δ) (hp : 1 ≤ p) :
    MemLp (iteratedDeriv r (Interval.smooth r δ f)) p volume := by
  have h2 : (2 : ℝ≥0∞) ^ r < ∞ := ENNReal.pow_lt_top ENNReal.ofNat_lt_top
  have hinv : (ENNReal.ofReal δ)⁻¹ < ∞ := ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hδ)
  refine memLp_iff.2 ?_
  calc eLpNorm (iteratedDeriv r (Interval.smooth r δ f)) p volume
      ≤ 2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * Rd.modulus volume r p f (r * δ) :=
        eLpNorm_iteratedDeriv_smooth_le_modulus hf r hδ hp
    _ ≤ 2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * (2 ^ r * eLpNorm f p volume) := by
        gcongr
        exact Rd.modulus_le hf.aestronglyMeasurable hp r _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top h2 (ENNReal.pow_lt_top hinv))
        (ENNReal.mul_lt_top h2 hfp.eLpNorm_lt_top)

end Daubechies
