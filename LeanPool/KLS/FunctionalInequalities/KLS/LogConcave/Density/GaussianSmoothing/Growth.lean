/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Posterior
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives
public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.Log
public import LeanPool.KLS.FunctionalInequalities.Analysis.TemperateGrowth

/-!
# Polynomial growth of the derivatives of the Gaussian-smoothed potential

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: every derivative
of `V_s = −log(ρ * γ_s)` has polynomial growth. Along an increment `u` at the base point `x`, the
smoothed density factors through the centered posterior `Q_x`:
`V_s(x+u) = V_s(x) + s‖u‖² − 2s⟪m_x − x, u⟫ − Λ_{Q_x}(2s·u)`, so `D^n V_s(x) = −(2s)^n D^n
Λ_{Q_x}(0)`
for `n ≥ 3`. The centered posterior has all exponential moments (completing the square), its
Laplace derivatives at `0` are the moment tensors bounded by the uniform quantitative Borell moments
(`Posterior`), the local log-composition bound gives `‖D^n Λ_{Q_x}(0)‖ ≤ (n!)² D^n` with `D`
independent of `x`, and the temperate-growth constructor turns the uniform bounds of orders `≥ 3`
into `Function.HasTemperateGrowth`. Constants depend on `n`, the dimension and `s`; nothing here is
dimension-free. Quadratic regularization, whitening and the convergence of the approximation are
separate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section CenteredFactorization

omit [CompleteSpace E]

/--
The centered posterior has every exponential moment `∫ e^{t‖y‖} dQ_x < ∞` (completing the square
under the Gaussian weight; no moment of `μ` is needed). -/
theorem integrable_exp_norm_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x : E) (t : ℝ) :
    Integrable (fun y : E => Real.exp (t * ‖y‖)) (centeredPosteriorLaw μ hs x : Measure E) := by
  by_cases ht : 0 ≤ t
  · let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
    let m : E := ∫ y, y ∂P
    rw [coe_centeredPosteriorLaw]
    apply
      (integrable_map_measure (by fun_prop)
          (by fun_prop :
            AEMeasurable (fun y : E => y - ∫ z, z ∂(μ.tilted (fun z => -s * ‖x - z‖ ^ 2))) _)).2
    change Integrable (fun y : E => Real.exp (t * ‖y - m‖)) P
    rw [integrable_tilted_iff (integrable_shiftedKernel μ hs x)]
    let C : ℝ := t ^ 2 / (4 * s) + t * ‖x - m‖
    refine (integrable_const (Real.exp C)).mono' (by fun_prop) ?_
    filter_upwards [] with y
    simp only [smul_eq_mul,
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have htri : ‖y - m‖ ≤ ‖y - x‖ + ‖x - m‖ := by
      rw [show y - m = (y - x) + (x - m) by abel]
      exact norm_add_le _ _
    have hquad : t * ‖y - x‖ - s * ‖y - x‖ ^ 2 ≤ t ^ 2 / (4 * s) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
      nlinarith [sq_nonneg (2 * s * ‖y - x‖ - t)]
    have hmul := mul_le_mul_of_nonneg_left htri ht
    rw [norm_sub_rev x y]
    dsimp only [C]
    nlinarith
  · refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) (norm_nonneg y))

/--
The MGF of the score under `P_x` at `1` is `e^{2s⟪m_x − x, u⟫}` times the Laplace transform of the
centered posterior at `2s·u`. -/
theorem mgf_score_eq_laplace_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x u : E) :
    mgf (fun y => 2 * s * ⟪y - x, u⟫) (μ.tilted (fun y => -s * ‖x - y‖ ^ 2)) 1 =
      Real.exp (2 * s * ⟪(∫ y, y ∂(μ.tilted (fun y => -s * ‖x - y‖ ^ 2))) - x, u⟫) *
        ∫ y, Real.exp ⟪(2 * s) • u, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E) := by
  let P := μ.tilted (fun y => -s * ‖x - y‖ ^ 2)
  let m : E := ∫ y, y ∂P
  have heq (y : E) :
    Real.exp (2 * s * ⟪y - x, u⟫) =
      Real.exp (2 * s * ⟪m - x, u⟫) * Real.exp ⟪(2 * s) • u, y - m⟫ := by
    rw [← Real.exp_add]
    congr 1
    rw [show y - x = (m - x) + (y - m) by abel, inner_add_left, real_inner_smul_left]
    have hi : ⟪u, y - m⟫ = ⟪y - m, u⟫ := (real_inner_comm u (y - m)).symm
    rw [hi]
    ring
  rw [coe_centeredPosteriorLaw,
    integral_map
      (by fun_prop :
        AEMeasurable (fun y : E => y - ∫ z, z ∂(μ.tilted (fun z => -s * ‖x - z‖ ^ 2))) _)
      (by fun_prop : AEStronglyMeasurable (fun y : E => Real.exp ⟪(2 * s) • u, y⟫) _)]
  unfold mgf
  simp only [one_mul]
  change
    (∫ y, Real.exp (2 * s * ⟪y - x, u⟫) ∂P) =
      Real.exp (2 * s * ⟪m - x, u⟫) * ∫ y, Real.exp ⟪(2 * s) • u, y - m⟫ ∂P
  have hfun :
    (fun y => Real.exp (2 * s * ⟪y - x, u⟫)) = fun y =>
      Real.exp (2 * s * ⟪m - x, u⟫) * Real.exp ⟪(2 * s) • u, y - m⟫ :=
    funext heq
  rw [hfun, integral_const_mul]

/-- `F(x+u) = F(x) e^{−s‖u‖² + 2s⟪m_x − x, u⟫} L_{Q_x}(2s·u)` for the smoothed density. -/
theorem normalizedDensity_centered_factorization {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x u : E) :
    normalizedDensity ρ s (x + u) = normalizedDensity ρ s x *
      Real.exp (-s * ‖u‖ ^ 2 + 2 * s *
        ⟪(∫ y, y ∂(μ.tilted (fun y => -s * ‖x - y‖ ^ 2))) - x, u⟫) *
          ∫ y, Real.exp ⟪(2 * s) • u, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E) := by
  have h := normalizedDensity_line_factorization hρ hs x u 1
  simp only [one_smul, one_pow, mul_one] at h
  rw [mgf_score_eq_laplace_centeredPosteriorLaw μ hs x u] at h
  rw [Real.exp_add]
  exact h.trans (by ring)

/-- `V(x+u) = V(x) + s‖u‖² − 2s⟪m_x − x, u⟫ − Λ_{Q_x}(2s·u)` for the smoothed potential. -/
theorem potential_centered_factorization {μ : Measure E} [IsProbabilityMeasure μ] {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x u : E) :
    potential ρ s (x + u) =
      potential ρ s x + s * ‖u‖ ^ 2 -
          2 * s * ⟪(∫ y, y ∂(μ.tilted (fun y => -s * ‖x - y‖ ^ 2))) - x, u⟫ -
        logLaplace (centeredPosteriorLaw μ hs x : Measure E) ((2 * s) • u) := by
  have hi :
    Integrable (fun y => Real.exp ⟪(2 * s) • u, y⟫) (centeredPosteriorLaw μ hs x : Measure E) := by
    refine
      (integrable_exp_norm_centeredPosteriorLaw μ hs x ‖(2 * s) • u‖).mono' (by fun_prop) ?_
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (real_inner_le_norm _ _)
  have hp : 0 < ∫ y, Real.exp ⟪(2 * s) • u, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E) :=
    integral_exp_pos hi
  unfold potential logLaplace
  rw [normalizedDensity_centered_factorization hρ hs,
    Real.log_mul (mul_pos (normalizedDensity_pos hρ hs x) (Real.exp_pos _)).ne' hp.ne',
    Real.log_mul (normalizedDensity_pos hρ hs x).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

section PolynomialDerivatives

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem linear_iterated_ge_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {n : ℕ} (hn : 2 ≤ n) (x : E) : iteratedFDeriv ℝ n L x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k = (k + 1) + 1 by omega]
  ext h
  rw [iteratedFDeriv_succ_apply_right]
  have hfd : fderiv ℝ L = fun _ : E => L := funext fun y => L.fderiv
  rw [hfd, iteratedFDeriv_succ_const]
  rfl

private theorem norm_sq_iterated_ge_three {n : ℕ} (hn : 3 ≤ n) (x : E) :
    iteratedFDeriv ℝ n (fun y : E => ‖y‖ ^ 2) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + k = (k + 2) + 1 by omega]
  let L : E →L[ℝ] E →L[ℝ] ℝ := (2 : ℝ) • innerSL ℝ
  have hfd : fderiv ℝ (fun y : E => ‖y‖ ^ 2) = L := by
    ext y z
    simp [L, fderiv_norm_sq_apply, two_smul, innerSL_apply_apply]
    rfl
  ext h
  rw [iteratedFDeriv_succ_apply_right, hfd, linear_iterated_ge_two L (by omega)]
  simp

end PolynomialDerivatives


/-- The cumulant generating function of the centered posterior is smooth on all of `E`. -/
theorem contDiff_logLaplace_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x : E) :
    ContDiff ℝ ∞ (logLaplace (centeredPosteriorLaw μ hs x : Measure E)) :=
  contDiff_logLaplace _ (integrable_exp_norm_centeredPosteriorLaw μ hs x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic polynomial part has vanishing derivatives of order `≥ 3`. -/
private theorem centered_polynomial_iterated_zero (a s : ℝ) (m : E) {n : ℕ} (hn : 3 ≤ n) :
    iteratedFDeriv ℝ n (fun u : E => a + s * ‖u‖ ^ 2 - 2 * s * ⟪m, u⟫) 0 = 0 := by
  have hnorm : ContDiffAt ℝ n (fun u : E => ‖u‖ ^ 2) 0 := (contDiff_norm_sq ℝ).contDiffAt
  have hinner : ContDiffAt ℝ n (fun u : E => ⟪m, u⟫) 0 := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ m).contDiff.contDiffAt
  have hq : ContDiffAt ℝ n (fun u : E => s * ‖u‖ ^ 2) 0 := contDiffAt_const.mul hnorm
  have hl : ContDiffAt ℝ n (fun u : E => 2 * s * ⟪m, u⟫) 0 := contDiffAt_const.mul hinner
  rw [fun_iteratedFDeriv_sub_apply (contDiffAt_const.add hq) hl,
    fun_iteratedFDeriv_add_apply contDiffAt_const hq]
  have hc : iteratedFDeriv ℝ n (fun _ : E => a) 0 = 0 := by
    rw [iteratedFDeriv_const_of_ne (by omega : n ≠ 0)]
    rfl
  have hquad : iteratedFDeriv ℝ n (fun u : E => s * ‖u‖ ^ 2) 0 = 0 := by
    have heq : (fun u : E => s * ‖u‖ ^ 2) = fun u => s • ‖u‖ ^ 2 := by rfl
    rw [heq, iteratedFDeriv_const_smul_apply' hnorm, norm_sq_iterated_ge_three hn, smul_zero]
  have hlin : iteratedFDeriv ℝ n (fun u : E => 2 * s * ⟪m, u⟫) 0 = 0 := by
    let L : E →L[ℝ] ℝ := (2 * s) • innerSL ℝ m
    change iteratedFDeriv ℝ n L 0 = 0
    exact linear_iterated_ge_two L (by omega) 0
  rw [hc, hquad, hlin]
  simp

/--
**Higher derivatives of the smoothed potential**: `D^n V(x) = −(2s)^n D^n Λ_{Q_x}(0)` for `n ≥ 3`.
-/
theorem potential_iteratedFDeriv_ge_three {μ : Measure E} [IsProbabilityMeasure μ] {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (x : E) {n : ℕ} (hn : 3 ≤ n) :
    iteratedFDeriv ℝ n (potential ρ s) x =
      -((2 * s) ^ n) •
        iteratedFDeriv ℝ n (logLaplace (centeredPosteriorLaw μ hs x : Measure E)) 0 := by
  let G := logLaplace (centeredPosteriorLaw μ hs x : Measure E)
  let m : E := (∫ y, y ∂(μ.tilted (fun y => -s * ‖x - y‖ ^ 2))) - x
  let P : E → ℝ := fun u => potential ρ s x + s * ‖u‖ ^ 2 - 2 * s * ⟪m, u⟫
  have hG : ContDiff ℝ ∞ G := contDiff_logLaplace_centeredPosteriorLaw μ hs x
  have hGn : ContDiff ℝ n G := hG.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have hnorm : ContDiffAt ℝ n (fun u : E => ‖u‖ ^ 2) 0 := (contDiff_norm_sq ℝ).contDiffAt
  have hinner : ContDiffAt ℝ n (fun u : E => ⟪m, u⟫) 0 := by
    simpa only [coe_innerSL_apply] using (innerSL ℝ m).contDiff.contDiffAt
  have hP : ContDiffAt ℝ n P 0 :=
    (contDiffAt_const.add (contDiffAt_const.mul hnorm)).sub (contDiffAt_const.mul hinner)
  have hGs : ContDiffAt ℝ n (fun u => G ((2 * s) • u)) 0 := by fun_prop
  have heq : (fun u : E => potential ρ s (x + u)) = fun u => P u - G ((2 * s) • u) := by
    funext u
    exact potential_centered_factorization hρ hs x u
  have hshift :
    iteratedFDeriv ℝ n (potential ρ s) x =
      iteratedFDeriv ℝ n (fun u => potential ρ s (x + u)) 0 := by
    simpa only [add_zero] using (iteratedFDeriv_comp_add_left n x (0 : E)).symm
  rw [hshift, heq, fun_iteratedFDeriv_sub_apply hP hGs,
    centered_polynomial_iterated_zero (potential ρ s x) s m hn]
  have hscale := congrFun (iteratedFDeriv_comp_const_smul (2 * s) hGn) (0 : E)
  rw [hscale]
  simp only [smul_zero, zero_sub, neg_smul]
  rfl

end CenteredFactorization

/--
`‖D^d L_{Q_x}(0)‖ ≤ d!/q^d · C₀`, uniformly in the base point `x` (quantitative Borell moments). -/
theorem norm_iteratedFDeriv_laplace_centeredPosteriorLaw_le {μ : Measure E}
    [IsProbabilityMeasure μ] {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ}
    (hs : 0 < s) (x : E) (d : ℕ) :
    let R : ℝ := 2 * Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * s) + 1)
    ‖iteratedFDeriv ℝ d
          (fun z => ∫ y, Real.exp ⟪z, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E)) 0‖ ≤
      (d.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ d *
        ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have hr := centeredPosteriorRate_pos (E := E) hs
  have hi := (integral_exp_norm_centeredPosteriorLaw_le hρ hs x).1
  have hm := (integral_norm_pow_centeredPosteriorLaw_le hρ hs x d).2
  exact (norm_iteratedFDeriv_laplace_zero_le _ hr hi d).trans hm

/-- A single `D ≥ 1` with `‖D^i L_{Q_x}(0)‖ ≤ D^i` for `1 ≤ i ≤ n`, uniformly in `x`. -/
theorem exists_uniform_laplace_power_bound {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : E, ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i
        (fun z => ∫ y, Real.exp ⟪z, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E)) 0‖ ≤ D ^ i := by
  classical
  let R : ℝ := 2 * Real.sqrt ((Module.finrank ℝ E : ℝ) / (2 * s) + 1)
  let B : ℕ → ℝ := fun i =>
    (i.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ i *
      ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))))
  let D : ℝ := max 1 (∑ j ∈ Finset.range (n + 1), |B j|)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro x i hi hin
  have hsum : |B i| ≤ ∑ j ∈ Finset.range (n + 1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.2 (by omega))
  have hBD : B i ≤ D := (le_abs_self _).trans (hsum.trans (le_max_right _ _))
  have hDpow : D ≤ D ^ i := by
    have h := pow_le_pow_right₀ (le_max_left 1 (∑ j ∈ Finset.range (n + 1), |B j|)) hi
    simpa only [pow_one] using h
  exact (norm_iteratedFDeriv_laplace_centeredPosteriorLaw_le hρ hs x i).trans (hBD.trans hDpow)

section LaplaceRegularity

omit [CompleteSpace E]

/-- The Laplace transform of the centered posterior is smooth. -/
theorem contDiff_laplace_centeredPosteriorLaw (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x : E) :
    ContDiff ℝ ∞ (fun z => ∫ y, Real.exp ⟪z, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E)) := by
  have hgi : ∀ t : ℝ, Integrable (fun y : E => Real.exp (t * ‖y‖) * ‖(1 : ℝ)‖)
      (centeredPosteriorLaw μ hs x : Measure E) := by
    intro t
    simpa only [norm_one, mul_one] using integrable_exp_norm_centeredPosteriorLaw μ hs x t
  simpa only [smul_eq_mul, mul_one] using contDiff_integral_exp_inner_smul_of_integrable
    (centeredPosteriorLaw μ hs x : Measure E) measurable_const.aestronglyMeasurable hgi

/-- The Laplace transform of the centered posterior is positive. -/
theorem laplace_centeredPosteriorLaw_pos (μ : Measure E) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (x z : E) :
    0 < ∫ y, Real.exp ⟪z, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E) := by
  have hi : Integrable (fun y => Real.exp ⟪z, y⟫) (centeredPosteriorLaw μ hs x : Measure E) := by
    refine (integrable_exp_norm_centeredPosteriorLaw μ hs x ‖z‖).mono' (by fun_prop) ?_
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (real_inner_le_norm z y)
  exact integral_exp_pos hi

end LaplaceRegularity

/-- `‖D^n Λ_{Q_x}(0)‖ ≤ (n!)² D^n` uniformly in `x` (local log composition). -/
theorem exists_uniform_centered_logLaplace_derivative_bound {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : E,
      ‖iteratedFDeriv ℝ n (logLaplace (centeredPosteriorLaw μ hs x : Measure E)) 0‖ ≤
        (n.factorial : ℝ) ^ 2 * D ^ n := by
  obtain ⟨D, hD1, hD⟩ := exists_uniform_laplace_power_bound hρ hs n
  refine ⟨D, hD1, ?_⟩
  intro x
  let f : E → ℝ := fun z => ∫ y, Real.exp ⟪z, y⟫ ∂(centeredPosteriorLaw μ hs x : Measure E)
  have hf : ContDiffOn ℝ ∞ f Set.univ := (contDiff_laplace_centeredPosteriorLaw μ hs x).contDiffOn
  have hpos : ∀ y ∈ Set.univ, 0 < f y := fun y _ => laplace_centeredPosteriorLaw_pos μ hs x y
  have hone : f 0 = 1 := by dsimp only [f]; simp
  exact Analysis.norm_iteratedFDeriv_log_comp_le_factorial_sq isOpen_univ
    (Set.mem_univ (0 : E)) hf hpos hone (hD x)

/--
**Uniform bounds on the derivatives of order `≥ 3`** of the smoothed potential: `‖D^n V(x)‖ ≤ C_n`
with `C_n` depending on `n`, the dimension and `s` only. -/
theorem exists_uniform_potential_derivative_bound {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) {n : ℕ}
    (hn : 3 ≤ n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (potential ρ s) x‖ ≤ C := by
  obtain ⟨D, hD1, hD⟩ := exists_uniform_centered_logLaplace_derivative_bound hρ hs n
  let C : ℝ := (2 * s) ^ n * ((n.factorial : ℝ) ^ 2 * D ^ n)
  have hpow : 0 ≤ (2 * s) ^ n := pow_nonneg (mul_pos (by norm_num) hs).le n
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  refine ⟨C, mul_nonneg hpow (mul_nonneg (sq_nonneg _) (pow_nonneg hD0 n)), ?_⟩
  intro x
  rw [potential_iteratedFDeriv_ge_three hρ hs x hn, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_left (hD x) hpow

/-- **Polynomial growth of all derivatives of the smoothed potential** (BKL Section 2, p. 5):
`V_s = −log(ρ * γ_s)` has `Function.HasTemperateGrowth`, for every probability law with a Borell
density and every `s > 0`, in every finite dimension. -/
theorem potential_hasTemperateGrowth {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) :
    Function.HasTemperateGrowth (potential ρ s) := by
  apply Analysis.hasTemperateGrowth_of_bounded_high_derivatives
    (potential_contDiff_infty hρ hs)
  intro n hn
  obtain ⟨C, _hC0, hC⟩ := exists_uniform_potential_derivative_bound hρ hs hn
  exact ⟨C, hC⟩

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
