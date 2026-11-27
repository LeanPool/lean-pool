/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Torus.Lattice

/-!
# Periodisation and Poisson summation on `𝕋²`

For a Schwartz function `f` on `ℂ ≅ ℝ²` and `R > 0`:

* `HarmonicAnalysis.periodize R f (y) = Σ_{j ∈ ℤ²} f (R (y + j))`, a `ℤ²`-periodic function of
  `y ∈ ℂ` (the lattice `ℤ²` is `ℤ + iℤ`, `HarmonicAnalysis.latticePoint`);
* `HarmonicAnalysis.sampledCoeff R f (n) = R⁻² 𝓕 f (n / R)` for `n ≠ 0`, and `0` at `n = 0`.

## Main results

* `HarmonicAnalysis.summable_sampledCoeff`: these coefficients are summable.
* `HarmonicAnalysis.hasSum_periodize` (Poisson summation on `ℤ²`):
  `Σ_{j ∈ ℤ²} f (R (y + j)) = Σ_{n ∈ ℤ²} R⁻² 𝓕 f (n / R) e^{2πi ⟨n, y⟩}`, the Fourier series of
  the periodisation, which converges absolutely.
* `HarmonicAnalysis.tendsto_eLpNorm_tsum_fourier_mul_mFourier`, Lemma 5.7.5 of
  Hytönen–van Neerven–Veraar–Weis (HNVW) for `ℝ² ≅ ℂ` and scalar functions, with `ε = 1 / R`: for
  `1 ≤ p < ∞`, `R^{2/p} ‖Σ_n R⁻² 𝓕 f (n / R) e_n‖_{L^p (𝕋²)} → ‖f‖_{L^p (ℂ)}` as `R → ∞`.

The coefficients `sampledCoeff`, without the mean, serve only for the summability behind Poisson
summation, which enters the transference through Lemma 5.7.5.

## Proofs

Poisson summation by the standard argument: the series defining the periodisation converges
locally uniformly (Weierstrass M-test, with the Schwartz decay of `f` and Peetre's inequality
`HarmonicAnalysis.exists_norm_add_le`), so the periodisation is a continuous function on `𝕋²`
(`HarmonicAnalysis.torusLift`); its Fourier coefficients are the samples `R⁻² 𝓕 f (n / R)`
(`HarmonicAnalysis.mFourierCoeff_torusLift_periodize`: the translates of the centred cell tile
`ℂ`, then the change of variables `x = R y`), which are summable, and the Fourier series of a
continuous function with summable coefficients converges to it everywhere.

Lemma 5.7.5 by HNVW's argument (p. 461): Poisson summation; the change of variables `x = R y`, which
turns the norm over `𝕋²` into the norm over the cell `R · (−½, ½]²`
(`HarmonicAnalysis.ofReal_rpow_mul_eLpNorm_torus_eq_dilatedCell`); the decomposition
`Σ_j f (x + R j) = f (x) + Σ_{j ≠ 0} f (x + R j)` (`HarmonicAnalysis.periodize_div_eq`); the decay
`|f (x + R j)| ≤ C (R |j|)^{−3}` on the cell, so that the error is `O (R^{−3})` there
(`HarmonicAnalysis.exists_norm_tsum_ite_le`) and `O (R^{2/p − 3})` in `L^p`, by Minkowski's
inequality; and the norms of `f` over the cells, which tend to `‖f‖_p`. HNVW sums the norms of the
terms `f (· + R j)`, `j ≠ 0`; here they are summed pointwise first.

A correction to the source: HNVW does not say which cell of `R ℤ²` represents the dilated torus, and
the proof needs the centred one. On `R · [0, 1)²` (the book writes `𝕋^d = [0, 1]^d` on p. 113 and
integrates over `[0, 1)^d` in Lemma 5.7.3) the decay bound fails, as `x + R j` can be near `0` for
`j ≠ 0`, and the norms of `f` over these cells tend to its norm over `[0, ∞)²`. HNVW does not state
the range of `p` either; its `N > d > d / p` is for `p > 1`, and `N > d ≥ d / p` does for `p = 1`.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*, Ergebnisse
  der Mathematik 63, Springer, 2016: Lemma 5.7.5 (p. 461).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ENNReal

namespace HarmonicAnalysis

open UnitAddTorus

/-- The periodisation `y ↦ Σ_{j ∈ ℤ²} f (R (y + j))` of `x ↦ f (R x)`, a `ℤ²`-periodic function on
`ℂ`. -/
def periodize (R : ℝ) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  ∑' j : Fin 2 → ℤ, f (R * (y + latticePoint j))

/-- The coefficients `R⁻² 𝓕 f (n / R)` of the periodisation of `x ↦ f (R x)`, with the mean
(`n = 0`) removed. -/
def sampledCoeff (R : ℝ) (f : ℂ → ℂ) (n : Fin 2 → ℤ) : ℂ :=
  if n = 0 then 0 else ((R : ℂ) ^ 2)⁻¹ * 𝓕 f (latticePoint n / R)

/-- The coefficients `R⁻² 𝓕 f (n / R)` are summable: by the Schwartz decay of `𝓕 f`,
`|ξ|³ |𝓕 f (ξ)| ≤ C`, so `|R⁻² 𝓕 f (n / R)| ≤ C R |n|^{−3} ≤ C R ‖n‖_∞^{−3}` for `n ≠ 0`, and
`Σ_{n ≠ 0} ‖n‖_∞^{−3}` converges. -/
theorem summable_sampledCoeff (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) :
    Summable (sampledCoeff R f) := by
  -- Schwartz decay of `𝓕 f`: `|ξ|³ |𝓕 f (ξ)| ≤ C`.
  set C := SchwartzMap.seminorm ℝ 3 0 (𝓕 f)
  have hC : ∀ ξ : ℂ, ‖ξ‖ ^ 3 * ‖𝓕 (f : ℂ → ℂ) ξ‖ ≤ C := fun ξ => by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 f) 3 ξ
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
  -- For `n ≠ 0`: `R⁻² |𝓕 f (n / R)| ≤ R⁻² C (|n| / R)^{−3} ≤ C R ‖n‖_∞^{−3}`.
  refine Summable.of_norm_bounded (summable_inv_norm_pow_three.mul_left (C * R)) fun n => ?_
  by_cases hn : n = 0
  · simp [sampledCoeff, hn]
  have hn' : 0 < ‖n‖ := norm_pos_iff.2 hn
  have hle := norm_le_norm_latticePoint n
  have hpos : 0 < ‖latticePoint n‖ := hn'.trans_le hle
  have h1 := hC (latticePoint n / R)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_pow, div_mul_eq_mul_div,
    div_le_iff₀ (by positivity)] at h1
  rw [sampledCoeff, ite_eq_right hn, norm_mul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hR.le]
  have h2 : ‖𝓕 (f : ℂ → ℂ) (latticePoint n / R)‖ ≤ C * R ^ 3 / ‖latticePoint n‖ ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc (R ^ 2)⁻¹ * ‖𝓕 (f : ℂ → ℂ) (latticePoint n / R)‖
      ≤ (R ^ 2)⁻¹ * (C * R ^ 3 / ‖latticePoint n‖ ^ 3) := by gcongr
    _ ≤ (R ^ 2)⁻¹ * (C * R ^ 3 / ‖n‖ ^ 3) := by gcongr
    _ = C * R * (‖n‖ ^ 3)⁻¹ := by field_simp

/-! ### The periodisation -/

/-- Peetre's inequality for the weight `(1 + |x|)^{−3}`, for a Schwartz function `f`:
`|f (x + a)| ≤ C (1 + |x|)³ (1 + |a|)^{−3}`. -/
theorem exists_norm_add_le (f : 𝓢(ℂ, ℂ)) :
    ∃ C, 0 ≤ C ∧ ∀ x a : ℂ, ‖f (x + a)‖ ≤ C * (1 + ‖x‖) ^ 3 * ((1 + ‖a‖) ^ 3)⁻¹ := by
  set C := 2 ^ 3 * (Finset.Iic (3, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hC : ∀ z, (1 + ‖z‖) ^ 3 * ‖f z‖ ≤ C := fun z => by
    simpa [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) le_rfl le_rfl f z
  refine ⟨C, (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0), fun x a => ?_⟩
  have h1 : 1 + ‖a‖ ≤ (1 + ‖x‖) * (1 + ‖x + a‖) := by
    have := norm_sub_le (x + a) x
    rw [add_sub_cancel_left] at this
    nlinarith [norm_nonneg x, norm_nonneg (x + a)]
  have h2 : ‖f (x + a)‖ ≤ C * ((1 + ‖x + a‖) ^ 3)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm]
    exact hC _
  have h3 : ((1 + ‖x + a‖) ^ 3)⁻¹ ≤ (1 + ‖x‖) ^ 3 * ((1 + ‖a‖) ^ 3)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
      div_le_iff₀ (by positivity), ← mul_pow]
    gcongr
  calc ‖f (x + a)‖ ≤ C * ((1 + ‖x + a‖) ^ 3)⁻¹ := h2
    _ ≤ C * ((1 + ‖x‖) ^ 3 * ((1 + ‖a‖) ^ 3)⁻¹) := by gcongr
    _ = C * (1 + ‖x‖) ^ 3 * ((1 + ‖a‖) ^ 3)⁻¹ := by ring

/-- `Σ_{j ∈ ℤ²} (1 + R |j|)^{−3}` converges for `R > 0`. -/
theorem summable_inv_one_add_norm_pow_three {R : ℝ} (hR : 0 < R) :
    Summable fun j : Fin 2 → ℤ => ((1 + ‖(R : ℂ) * latticePoint j‖) ^ 3)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (summable_inv_norm_pow_three.mul_left (R ^ 3)⁻¹) ?_
  filter_upwards [eventually_cofinite_ne 0] with j hj
  have hj' : 0 < ‖j‖ := norm_pos_iff.2 hj
  rw [Real.norm_of_nonneg (by positivity), ← mul_inv, ← mul_pow]
  refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 3)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
  nlinarith [mul_le_mul_of_nonneg_left (norm_le_norm_latticePoint j) hR.le]

/-- The series `Σ_{j ∈ ℤ²} f (x + R j)` converges, for a Schwartz function `f` and `R > 0`. -/
theorem summable_comp_add_mul_latticePoint (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) (x : ℂ) :
    Summable fun j : Fin 2 → ℤ => f (x + R * latticePoint j) := by
  obtain ⟨C, -, hC⟩ := exists_norm_add_le f
  exact Summable.of_norm_bounded
    ((summable_inv_one_add_norm_pow_three hR).mul_left (C * (1 + ‖x‖) ^ 3)) fun j => hC x _

/-- The periodisation is `ℤ²`-periodic. -/
theorem periodize_add_latticePoint (R : ℝ) (f : ℂ → ℂ) (y : ℂ) (k : Fin 2 → ℤ) :
    periodize R f (y + latticePoint k) = periodize R f y := by
  have := (Equiv.addLeft k).tsum_eq (fun j => f (R * (y + latticePoint j)))
  simp only [Equiv.coe_addLeft, latticePoint_add, ← add_assoc] at this
  exact this

/-- The periodisation of a Schwartz function is continuous: on the ball `B (y₀, 1)`, the series
`Σ_j f (R (y + j))` converges uniformly (Weierstrass M-test, with Peetre's inequality). -/
theorem continuous_periodize (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) : Continuous (periodize R f) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_add_le f
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  have hon : ContinuousOn (fun y => ∑' j : Fin 2 → ℤ, f (R * (y + latticePoint j)))
      (Metric.ball y₀ 1) := by
    refine continuousOn_tsum (u := fun j => C * (1 + R * (‖y₀‖ + 1)) ^ 3 *
      ((1 + ‖(R : ℂ) * latticePoint j‖) ^ 3)⁻¹) (fun j => ?_)
      ((summable_inv_one_add_norm_pow_three hR).mul_left _) fun j y hy => ?_
    · exact (f.continuous.comp (by fun_prop)).continuousOn
    · rw [mul_add]
      refine (hC _ _).trans ?_
      have hy' : ‖y‖ ≤ ‖y₀‖ + 1 := by
        have := norm_sub_norm_le y y₀
        linarith [mem_ball_iff_norm.1 hy]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
      gcongr
  exact hon.continuousAt (Metric.ball_mem_nhds _ one_pos)

/-- Poisson summation, the Fourier coefficients: the `n`-th Fourier coefficient of the
periodisation of `x ↦ f (R x)`, as a function on `𝕋²`, is `R⁻² 𝓕 f (n / R)`. The integral over
the centred cell of `Σ_j e_{−n} (y + j) f (R (y + j))` is, as the translates of the cell tile `ℂ`,
the integral over `ℂ` of `e_{−n} (y) f (R y)`; the change of variables `x = R y` concludes. -/
theorem mFourierCoeff_torusLift_periodize (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R)
    (n : Fin 2 → ℤ) :
    mFourierCoeff (torusLift (periodize R f)) n =
      ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_add_le f
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  -- The integrand `h (y) = e_{−n} (y) f (R y)` on `ℂ`.
  set e : ℂ → ℂ := fun y => mFourier (-n) (ofComplex y)
  set h : ℂ → ℂ := fun y => e y * f (R * y) with hh_def
  have he : Continuous e := (mFourier (-n)).continuous.comp continuous_ofComplex
  have he1 : ∀ y, ‖e y‖ = 1 := fun y => norm_mFourier_apply _ _
  have he_add : ∀ y k, e (y + latticePoint k) = e y := fun y k => by
    simp only [e, ofComplex_add_latticePoint]
  have hhc : Continuous h := he.mul (f.continuous.comp (continuous_const.mul continuous_id))
  have hint : Integrable h := by
    have h1 : Integrable fun y : ℂ => f (R • y) := f.integrable.comp_smul hR.ne'
    refine h1.mono hhc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    simp [h, he1, Complex.real_smul]
  -- The coefficient as an integral over the centred cell.
  rw [mFourierCoeff_eq_integral_centredCell]
  simp_rw [torusLift_ofComplex (periodize_add_latticePoint R f)]
  have step1 : ∀ y, mFourier (-n) (ofComplex y) • periodize R f y =
      ∑' j : Fin 2 → ℤ, h (y + latticePoint j) := fun y => by
    simp only [periodize, smul_eq_mul, h, he_add, ← tsum_mul_left]
    rfl
  simp_rw [step1]
  -- Exchange of the sum and the integral over the cell.
  have hFint : ∀ j : Fin 2 → ℤ,
      Integrable (fun y => h (y + latticePoint j)) (volume.restrict centredCell) := fun j =>
    ((hhc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set centredCell_subset_closedBall
  have hbd : ∀ j : Fin 2 → ℤ, ∀ y ∈ centredCell, ‖‖h (y + latticePoint j)‖‖ ≤
      C * (1 + R) ^ 3 * ((1 + ‖(R : ℂ) * latticePoint j‖) ^ 3)⁻¹ := fun j y hy => by
    have hy1 : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 (centredCell_subset_closedBall hy)
    rw [norm_norm, hh_def]
    simp only [norm_mul, he1, one_mul]
    rw [mul_add]
    refine (hC _ _).trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    gcongr
    nlinarith
  have hFsum : Summable fun j : Fin 2 → ℤ =>
      ∫ y in centredCell, ‖h (y + latticePoint j)‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (((summable_inv_one_add_norm_pow_three hR).mul_left (C * (1 + R) ^ 3)).mul_right
        (volume.real centredCell))
    exact (le_abs_self _).trans
      (norm_setIntegral_le_of_norm_le_const volume_centredCell_lt_top (hbd j))
  rw [← integral_tsum_of_summable_integral_norm hFint hFsum,
    (hasSum_integral_centredCell_add hint).tsum_eq]
  -- The change of variables `x = R y`.
  have h4 : 𝓕 (f : ℂ → ℂ) (latticePoint n / R) = (R : ℂ) ^ 2 * ∫ y, h y := by
    rw [Real.fourier_eq']
    have hpt : ∀ v : ℂ, Complex.exp (↑(-2 * Real.pi * inner ℝ v (latticePoint n / R)) *
        Complex.I) • f v = h (R⁻¹ • v) := fun v => by
      simp only [h, e, Complex.real_smul, smul_eq_mul, mFourier_ofComplex]
      congr 1
      · congr 1
        simp [Complex.inner, latticePoint_neg]
        ring
      · congr 1
        push_cast
        field_simp
    simp_rw [hpt]
    rw [Measure.integral_comp_inv_smul_of_nonneg volume h hR.le,
      Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin,
      Complex.real_smul]
    push_cast
    rfl
  rw [h4]
  field_simp

/-- Poisson summation on `ℤ²`: `Σ_{j ∈ ℤ²} f (R (y + j)) = Σ_{n ∈ ℤ²} R⁻² 𝓕 f (n / R) e_n (y)`.
The standard argument: the periodisation is continuous and `ℤ²`-periodic, so it is a continuous
function on `𝕋²`; its Fourier coefficients are the samples `R⁻² 𝓕 f (n / R)` of `𝓕 f`
(`HarmonicAnalysis.mFourierCoeff_torusLift_periodize`), which are summable
(`HarmonicAnalysis.summable_sampledCoeff`), so its Fourier series converges to it everywhere. -/
theorem hasSum_periodize (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) (y : ℂ) :
    HasSum (fun n : Fin 2 → ℤ =>
        ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R) * mFourier n (ofComplex y))
      (periodize R f y) := by
  let P : C(UnitAddTorus (Fin 2), ℂ) :=
    ⟨torusLift (periodize R f), continuous_torusLift (periodize_add_latticePoint R f)
      (continuous_periodize f hR)⟩
  have hcoeff : mFourierCoeff P = fun n : Fin 2 → ℤ =>
      ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R) :=
    funext (mFourierCoeff_torusLift_periodize f hR)
  have hsum : Summable (mFourierCoeff P) := by
    rw [hcoeff]
    convert (summable_sampledCoeff f hR).update 0
      (((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint 0 / R)) using 1
    funext n
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [Function.update, hn, sampledCoeff]
  have := hasSum_mFourier_series_apply_of_summable hsum (ofComplex y)
  rw [hcoeff] at this
  convert this using 1
  exact (torusLift_ofComplex (periodize_add_latticePoint R f) y).symm

/-! ### The `L^p` norms of the periodisations -/

/-- The periodisation, rescaled: `Σ_j f (R (x / R + j)) = f (x) + Σ_{j ≠ 0} f (x + R j)`. -/
theorem periodize_div_eq (f : 𝓢(ℂ, ℂ)) {R : ℝ} (hR : 0 < R) (x : ℂ) :
    periodize R f (x / R) =
      f x + ∑' j : Fin 2 → ℤ, if j = 0 then 0 else f (x + R * latticePoint j) := by
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have h : ∀ j, (R : ℂ) * (x / R + latticePoint j) = x + R * latticePoint j := fun j => by
    field_simp
  simp only [periodize, h]
  rw [(summable_comp_add_mul_latticePoint f hR x).tsum_eq_add_tsum_ite 0]
  simp

/-- On the dilated cell `R · (−½, ½]²`: `R ‖j‖_∞ ≤ 2 |x + R j|` for `j ∈ ℤ²`. -/
theorem mul_norm_le_two_mul_norm_add {R : ℝ} (hR : 0 < R) {x : ℂ} (hx : x / R ∈ centredCell)
    (j : Fin 2 → ℤ) : R * ‖j‖ ≤ 2 * ‖x + R * latticePoint j‖ := by
  rw [div_mem_centredCell_iff hR] at hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  set z := x + R * latticePoint j
  have key : ∀ (a : ℝ) (m : ℤ), -(R / 2) < a → a ≤ R / 2 → |a + R * m| ≤ ‖z‖ →
      R * ‖m‖ ≤ 2 * ‖z‖ := by
    intro a m ha1 ha2 hle
    rw [Int.norm_eq_abs]
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have hRm : R * |(m : ℝ)| ≤ |a + R * m| + |a| := by
      calc R * |(m : ℝ)| = |(a + R * m) - a| := by
            rw [add_sub_cancel_left, abs_mul, abs_of_pos hR]
        _ ≤ |a + R * m| + |a| := abs_sub _ _
    have ha : |a| ≤ R / 2 := abs_le.2 ⟨ha1.le, ha2⟩
    nlinarith [mul_le_mul_of_nonneg_left hm1 hR.le]
  have hn : 0 ≤ 2 * ‖z‖ / R := by positivity
  have : ‖j‖ ≤ 2 * ‖z‖ / R := by
    refine (pi_norm_le_iff_of_nonneg hn).2 fun i => ?_
    rw [le_div_iff₀ hR, mul_comm]
    fin_cases i
    · exact key _ _ h1 h2 (by simpa [z] using Complex.abs_re_le_norm z)
    · exact key _ _ h3 h4 (by simpa [z] using Complex.abs_im_le_norm z)
  rwa [le_div_iff₀ hR, mul_comm] at this

/-- The error of the rescaled periodisation on the dilated cell:
`|Σ_{j ≠ 0} f (x + R j)| ≤ K R^{−3}` for `x ∈ R · (−½, ½]²`. With `|z|³ |f (z)| ≤ C` and
`|x + R j| ≥ R ‖j‖_∞ / 2`, `K = 8 C Σ_{j ≠ 0} ‖j‖_∞^{−3}`. -/
theorem exists_norm_tsum_ite_le (f : 𝓢(ℂ, ℂ)) : ∃ K, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ x : ℂ,
    x / R ∈ centredCell →
      ‖∑' j : Fin 2 → ℤ, if j = 0 then 0 else f (x + R * latticePoint j)‖ ≤ K * (R ^ 3)⁻¹ := by
  set C := SchwartzMap.seminorm ℝ 3 0 f
  have hC : ∀ z, ‖z‖ ^ 3 * ‖f z‖ ≤ C := fun z => SchwartzMap.norm_pow_mul_le_seminorm ℝ f 3 z
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
  set S := ∑' j : Fin 2 → ℤ, (‖j‖ ^ 3)⁻¹
  have hS : 0 ≤ S := tsum_nonneg fun j => by positivity
  refine ⟨8 * C * S, by positivity, fun R hR x hx => ?_⟩
  refine (tsum_of_norm_bounded (summable_inv_norm_pow_three.hasSum.mul_left
    (8 * C * (R ^ 3)⁻¹)) fun j => ?_).trans_eq (by ring)
  by_cases hj : j = 0
  · simp [hj]
  rw [ite_eq_right hj]
  have hj' : 0 < ‖j‖ := norm_pos_iff.2 hj
  set z := x + R * latticePoint j
  have hz : R * ‖j‖ / 2 ≤ ‖z‖ := by linarith [mul_norm_le_two_mul_norm_add hR hx j]
  have hpos : 0 < R * ‖j‖ / 2 := div_pos (mul_pos hR hj') two_pos
  have h1 : ‖f z‖ ≤ C / ‖z‖ ^ 3 := by
    rw [le_div_iff₀ (pow_pos (hpos.trans_le hz) 3), mul_comm]
    exact hC z
  calc ‖f z‖ ≤ C / ‖z‖ ^ 3 := h1
    _ ≤ C / (R * ‖j‖ / 2) ^ 3 := by gcongr
    _ = 8 * C * (R ^ 3)⁻¹ * (‖j‖ ^ 3)⁻¹ := by field_simp; ring

/-- The measure of the dilated cell `R · (−½, ½]²` is `R²`. -/
private theorem volume_dilatedCell {R : ℝ} (hR : 0 < R) :
    volume {y : ℂ | y / R ∈ centredCell} = ENNReal.ofReal (R ^ 2) := by
  have h := setLIntegral_dilatedCell (fun _ => (1 : ℝ≥0∞)) hR
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul] at h
  rw [h, volume_pi, Measure.pi_univ]
  simp

/-- The estimate in the proof of HNVW, Lemma 5.7.5, for `1 ≤ p` and `R > 0`: by Poisson summation,
`R^{2/p} ‖Σ_n R⁻² 𝓕 f (n / R) e_n‖_{L^p (𝕋²)}` is the `L^p` norm of `Σ_j f (x + R j)` over the
dilated cell `Q_R = R · (−½, ½]²`, of measure `R²`. There `Σ_j f (x + R j) = f (x) + O (R^{−3})`, so
by Minkowski's inequality it differs from `‖f 1_{Q_R}‖_p` by at most `K R^{−3} R^{2/p}`. -/
private theorem exists_eLpNorm_periodize_le (f : 𝓢(ℂ, ℂ)) {p : ℝ} (hp : 1 ≤ p) :
    ∃ K, 0 ≤ K ∧ ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (2 / p)) * eLpNorm (fun x => ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ *
          𝓕 (f : ℂ → ℂ) (latticePoint n / R) * mFourier n x) (ENNReal.ofReal p) volume ≤
        eLpNorm ({y : ℂ | y / R ∈ centredCell}.indicator f) (ENNReal.ofReal p) volume +
          ENNReal.ofReal (K * (R ^ 3)⁻¹ * R ^ (2 / p)) ∧
      eLpNorm ({y : ℂ | y / R ∈ centredCell}.indicator f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (R ^ (2 / p)) * eLpNorm (fun x => ∑' n : Fin 2 → ℤ, ((R : ℂ) ^ 2)⁻¹ *
          𝓕 (f : ℂ → ℂ) (latticePoint n / R) * mFourier n x) (ENNReal.ofReal p) volume +
          ENNReal.ofReal (K * (R ^ 3)⁻¹ * R ^ (2 / p)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_tsum_ite_le f
  have hp0 : 0 < p := by linarith
  have hP : 1 ≤ ENNReal.ofReal p := by simpa using hp
  refine ⟨K, hK0, fun R hR => ?_⟩
  rw [ofReal_rpow_mul_eLpNorm_torus_eq_dilatedCell _ hp0 hR]
  -- Poisson summation.
  simp_rw [fun y => (hasSum_periodize f hR y).tsum_eq]
  set Q := {y : ℂ | y / R ∈ centredCell}
  have hQ : MeasurableSet Q := measurableSet_dilatedCell R
  set B := K * (R ^ 3)⁻¹
  have hB : 0 ≤ B := by positivity
  set G : ℂ → ℂ := Q.indicator fun y => periodize R f (y / R)
  -- The error on the dilated cell.
  have hE : eLpNorm (fun y => G y - Q.indicator f y) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (B * R ^ (2 / p)) := by
    have hm : AEStronglyMeasurable (fun y => G y - Q.indicator f y) volume :=
      ((((continuous_periodize f hR).comp (continuous_id.div_const _)).aestronglyMeasurable
        (μ := volume)).indicator hQ).sub (f.continuous.aestronglyMeasurable.indicator hQ)
    have hpt : ∀ y, ‖G y - Q.indicator f y‖ ≤ Q.indicator (fun _ => B) y := by
      intro y
      by_cases hy : y ∈ Q
      · simp only [G, Set.indicator_of_mem hy]
        rw [periodize_div_eq f hR, add_sub_cancel_left]
        exact hK R hR y hy
      · simp [G, Set.indicator_of_notMem hy]
    refine (eLpNorm_mono_real hm hpt).trans_eq ?_
    rw [eLpNorm_indicator_const hQ.nullMeasurableSet (by simpa using hp0) ENNReal.ofReal_ne_top,
      volume_dilatedCell hR, Real.eNorm_eq_ofReal hB, ENNReal.toReal_ofReal hp0.le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← ENNReal.ofReal_mul hB,
      ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 3
    push_cast
    ring
  constructor
  · have h := eLpNorm_add_le (μ := volume) hP (f := Q.indicator f)
      (g := fun y => G y - Q.indicator f y)
    rw [show (Q.indicator f + fun y => G y - Q.indicator f y) = G by ext y; simp] at h
    exact h.trans (by gcongr)
  · have h := eLpNorm_sub_le (μ := volume) hP (f := G) (g := fun y => G y - Q.indicator f y)
    rw [show (G - fun y => G y - Q.indicator f y) = Q.indicator f by ext y; simp] at h
    exact h.trans (by gcongr)

/-- **HNVW, Lemma 5.7.5** (for `ℝ² ≅ ℂ` and scalar functions, with `ε = 1 / R`, so that
`ε^{2/p'} 𝓕 f (ε n) = R^{2/p} R⁻² 𝓕 f (n / R)`): for a Schwartz function `f` and `1 ≤ p < ∞`,
`R^{2/p} ‖Σ_{n ∈ ℤ²} R⁻² 𝓕 f (n / R) e_n‖_{L^p (𝕋²)} → ‖f‖_{L^p (ℂ)}` as `R → ∞`. -/
theorem tendsto_eLpNorm_tsum_fourier_mul_mFourier (f : 𝓢(ℂ, ℂ)) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (R ^ (2 / p)) * eLpNorm (fun x => ∑' n : Fin 2 → ℤ,
        ((R : ℂ) ^ 2)⁻¹ * 𝓕 (f : ℂ → ℂ) (latticePoint n / R) * mFourier n x) (ENNReal.ofReal p)
        volume) atTop (nhds (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume)) := by
  obtain ⟨K, hK0, hK⟩ := exists_eLpNorm_periodize_le f hp
  have hp0 : 0 < p := by linarith
  -- The error term tends to `0`, because `2 / p − 3 < 0`.
  have herr : Tendsto (fun R : ℝ => ENNReal.ofReal (K * (R ^ 3)⁻¹ * R ^ (2 / p))) atTop
      (nhds 0) := by
    have h2p : 2 / p < 3 := by rw [div_lt_iff₀ hp0]; linarith
    have h := (tendsto_rpow_neg_atTop (y := 3 - 2 / p) (by linarith)).const_mul K
    rw [mul_zero] at h
    have h' : Tendsto (fun R : ℝ => K * (R ^ 3)⁻¹ * R ^ (2 / p)) atTop (nhds 0) := by
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with R hR
      rw [show -(3 - 2 / p) = 2 / p - ((3 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_sub_natCast hR.ne']
      ring
    simpa using ENNReal.tendsto_ofReal h'
  -- The norms over the dilated cells exhaust the norm over `ℂ`.
  have hcell : Tendsto (fun R : ℝ => eLpNorm ({y : ℂ | y / R ∈ centredCell}.indicator f)
      (ENNReal.ofReal p) volume) atTop (nhds (eLpNorm (f : ℂ → ℂ) (ENNReal.ofReal p) volume)) := by
    have hm : ∀ R : ℝ, AEStronglyMeasurable ({y : ℂ | y / R ∈ centredCell}.indicator f) volume :=
      fun R => f.continuous.aestronglyMeasurable.indicator (measurableSet_dilatedCell R)
    have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    simp_rw [fun R => eLpNorm_eq_lintegral_rpow_eNorm_toReal hP0 ENNReal.ofReal_ne_top (hm R)]
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hP0 ENNReal.ofReal_ne_top
      f.continuous.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    have hfm : Measurable fun y : ℂ => ‖f y‖ₑ ^ p := f.continuous.eNorm.measurable.pow_const p
    have hcell' : ∀ (R : ℝ) (y : ℂ), ‖{y : ℂ | y / R ∈ centredCell}.indicator f y‖ₑ ^ p =
        {y : ℂ | y / R ∈ centredCell}.indicator (fun y => ‖f y‖ₑ ^ p) y := fun R y => by
      by_cases hy : y ∈ {y : ℂ | y / R ∈ centredCell}
      · simp only [Set.indicator_of_mem hy]
      · simp only [Set.indicator_of_notMem hy, eNorm_zero, ENNReal.zero_rpow_of_pos hp0]
    simp_rw [hcell']
    refine (tendsto_lintegral_filter_of_dominated_convergence (fun y => ‖f y‖ₑ ^ p)
      (Eventually.of_forall fun R => hfm.indicator (measurableSet_dilatedCell R))
      (Eventually.of_forall fun R => ae_of_all _ fun y => Set.indicator_le_self _ _ y) ?_
      (ae_of_all _ fun y => ?_)).ennrpow_const _
    · have := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hP0 ENNReal.ofReal_ne_top
        (f.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top
      rw [ENNReal.toReal_ofReal hp0.le] at this
      exact this.ne
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_div_mem_centredCell y] with R hR
      exact (Set.indicator_of_mem (s := {y : ℂ | y / R ∈ centredCell}) (a := y) hR
        fun y => ‖f y‖ₑ ^ p).symm
  have hlow := ENNReal.Tendsto.sub hcell herr (Or.inl
    (f.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top.ne)
  rw [tsub_zero] at hlow
  have hupp := hcell.add herr
  rw [add_zero] at hupp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact tsub_le_iff_right.2 (hK R hR).2
  · filter_upwards [eventually_gt_atTop 0] with R hR
    exact (hK R hR).1

end HarmonicAnalysis
