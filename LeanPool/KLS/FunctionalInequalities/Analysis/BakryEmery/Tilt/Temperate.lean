/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.ExponentialMoments.Norm
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Gamma
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The tilt identities for tests of temperate growth

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 3.6 for scalar functions of the class `𝒜` (smooth,
every derivative of polynomial growth; Mathlib's `Function.HasTemperateGrowth`). The measure is
`μ = m.tilted (-V)` with `V ∈ C¹`, `∇V` of polynomial growth (true for the source's regular
measures,
whose Hessian is bounded) and all exponential moments. The compactly supported case is
`Analysis/BakryEmery/Tilt/Basic.lean`; here a scaled bump cutoff `χ_R(x) = φ(x / R)` and dominated
convergence remove the support condition from the integrated generator identity `∫ ℒu dμ_z = 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### The cutoff -/

/-- The bump `φ` on `E`: one on the closed unit ball, zero outside the ball of radius `2`. -/
def unitBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The scaled cutoff `χ_R(x) = φ(x / R)`. -/
def cutoff (R : ℝ) (x : E) : ℝ := (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_cutoff (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) := by
    change ContDiff ℝ ∞
      (fun x : E => (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x))
    exact unitBump.contDiff.comp (contDiff_const_smul R⁻¹)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff (E := E) R) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) ?_
    intro x hx
    have hxnorm : 2 * R < ‖x‖ := by
      have hnot : ¬‖x‖ ≤ 2 * R := by
        intro h
        apply hx
        simpa [Metric.closedBall, dist_zero_right] using h
      exact lt_of_not_ge hnot
    have hscale : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hmul : R⁻¹ * (2 * R) < R⁻¹ * ‖x‖ :=
      mul_lt_mul_of_pos_left hxnorm (inv_pos.mpr hR)
    have heq : R⁻¹ * (2 * R) = 2 := by
      calc
        R⁻¹ * (2 * R) = 2 * (R⁻¹ * R) := by ring
        _ = 2 := by rw [inv_mul_cancel₀ hR.ne', mul_one]
    have hnotball : R⁻¹ • x ∉ Metric.ball (0 : E) 2 := by
      intro h
      have hlt : ‖R⁻¹ • x‖ < 2 := by
        simpa [Metric.ball, dist_zero_right] using h
      rw [hscale, ← heq] at hlt
      exact (not_lt_of_ge (le_of_lt hmul)) hlt
    have hs :
        Function.support (unitBump : ContDiffBump (0 : E)) =
          Metric.ball (0 : E) 2 := by
      simpa [unitBump] using
        (unitBump : ContDiffBump (0 : E)).support_eq
    by_contra hne
    apply hnotball
    rw [← hs]
    exact hne

section CutoffBounds

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : cutoff R x = 1 := by
    unfold cutoff
    apply (unitBump : ContDiffBump (0 : E)).one_of_mem_closedBall
    have hdiv : ‖x‖ / R ≤ 1 := by
      exact (div_le_iff₀ hR).2 (by
        simpa only [one_mul] using hx)
    have hnorm : ‖R⁻¹ • x‖ ≤ 1 := by
      calc
        ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
          rw [norm_smul]
          simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        _ = ‖x‖ / R := by
          simp [div_eq_mul_inv, mul_comm]
        _ ≤ 1 := hdiv
    change dist (R⁻¹ • x) 0 ≤ 1
    simpa only [dist_zero_right] using hnorm

theorem abs_cutoff_le_one (R : ℝ) (x : E) : |cutoff R x| ≤ 1 := by
    change |(unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)| ≤ 1
    have hnonneg :
        0 ≤ (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) :=
      ContDiffBump.nonneg (unitBump : ContDiffBump (0 : E))
    have hle :
        (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x) ≤ 1 :=
      ContDiffBump.le_one (unitBump : ContDiffBump (0 : E))
    exact abs_le.2 ⟨by linarith, hle⟩

end CutoffBounds

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Uniform derivative bounds: for each order `n`, `‖∇ⁿχ_R‖ ≤ C` for every `R ≥ 1`. -/
theorem norm_iteratedFDeriv_cutoff_le (n : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ x : E, ‖iteratedFDeriv ℝ n (cutoff R) x‖ ≤ C := by
    have hcont :
        Continuous (fun x : E =>
          iteratedFDeriv ℝ n
            ((unitBump : ContDiffBump (0 : E)) : E → ℝ) x) := by
      exact
        (unitBump : ContDiffBump (0 : E)).contDiff
          |>.continuous_iteratedFDeriv (n := n) (by simp)
    have hcomp :
        HasCompactSupport (fun x : E =>
          iteratedFDeriv ℝ n
            ((unitBump : ContDiffBump (0 : E)) : E → ℝ) x) :=
      (unitBump : ContDiffBump (0 : E)).hasCompactSupport.iteratedFDeriv n
    obtain ⟨C₀, hC₀⟩ :=
      hcont.bounded_above_of_compact_support hcomp
    let C : ℝ := max C₀ 0
    have hC : ∀ x : E,
        ‖iteratedFDeriv ℝ n
            ((unitBump : ContDiffBump (0 : E)) : E → ℝ) x‖ ≤ C := by
      intro x
      exact (hC₀ x).trans (le_max_left _ _)
    have hC_nonneg : 0 ≤ C := le_max_right _ _
    refine ⟨C, ?_⟩
    intro R hR x
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have hinv : ‖R⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hR0)]
      exact inv_le_one_of_one_le₀ hR
    have hpow : ‖R⁻¹‖ ^ n ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) hinv
    have hderiv :
        iteratedFDeriv ℝ n (cutoff R) x =
          (R⁻¹) ^ n •
            iteratedFDeriv ℝ n
              ((unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • x) := by
      change
        iteratedFDeriv ℝ n
            (fun z : E =>
              ((unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • z)) x =
          (R⁻¹) ^ n •
            iteratedFDeriv ℝ n
              ((unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • x)
      simpa [inv_pow] using
        congrFun
          (iteratedFDeriv_comp_const_smul (𝕜 := ℝ)
            (f := ((unitBump : ContDiffBump (0 : E)) : E → ℝ))
            R⁻¹ (unitBump : ContDiffBump (0 : E)).contDiff) x
    calc
      ‖iteratedFDeriv ℝ n (cutoff R) x‖ =
          ‖R⁻¹‖ ^ n *
            ‖iteratedFDeriv ℝ n
              ((unitBump : ContDiffBump (0 : E)) : E → ℝ) (R⁻¹ • x)‖ := by
        rw [hderiv, norm_smul, norm_pow]
      _ ≤ ‖R⁻¹‖ ^ n * C :=
        mul_le_mul_of_nonneg_left (hC _) (pow_nonneg (norm_nonneg _) n)
      _ ≤ 1 * C :=
        mul_le_mul_of_nonneg_right hpow hC_nonneg
      _ = C := by simp

/-! ### Pointwise calculus -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `‖∇g(x)‖ = ‖∇¹g(x)‖`. -/
theorem norm_gradient_eq_norm_iteratedFDeriv_one (g : E → ℝ) (x : E) :
    ‖gradient g x‖ = ‖iteratedFDeriv ℝ 1 g x‖ := by
    rw [gradient, (InnerProductSpace.toDual ℝ E).symm.norm_map,
      norm_iteratedFDeriv_one]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- `|Δg(x)| ≤ dim E · ‖∇²g(x)‖`. -/
theorem abs_laplacian_le (g : E → ℝ) (x : E) :
    |Laplacian.laplacian g x| ≤ Module.finrank ℝ E * ‖iteratedFDeriv ℝ 2 g x‖ := by
    rw [laplacian_eq_sum_fderiv_fderiv]
    have hnorm (i : Fin (Module.finrank ℝ E)) :
        ‖(stdOrthonormalBasis ℝ E) i‖ = 1 :=
      (stdOrthonormalBasis ℝ E).norm_eq_one i
    have hterm (i : Fin (Module.finrank ℝ E)) :
        |(fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
            ((stdOrthonormalBasis ℝ E) i)| ≤
          ‖iteratedFDeriv ℝ 2 g x‖ := by
      have h :=
        (iteratedFDeriv ℝ 2 g x).le_opNorm
          ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
      rw [iteratedFDeriv_two_apply] at h
      simpa [Real.norm_eq_abs] using h
    calc
      |∑ i : Fin (Module.finrank ℝ E),
          (fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
            ((stdOrthonormalBasis ℝ E) i)| ≤
          ∑ i : Fin (Module.finrank ℝ E),
            |(fderiv ℝ (fderiv ℝ g) x ((stdOrthonormalBasis ℝ E) i))
              ((stdOrthonormalBasis ℝ E) i)| := by
        apply Finset.abs_sum_le_sum_abs
      _ ≤ ∑ i : Fin (Module.finrank ℝ E), ‖iteratedFDeriv ℝ 2 g x‖ := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 g x‖ := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The weighted Laplacian is local: functions agreeing near `x` have the same `ℒ` at `x`. -/
theorem weightedLaplacian_congr_of_eventuallyEq (V : E → ℝ) {f g : E → ℝ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : weightedLaplacian V f x = weightedLaplacian V g x := by
  rw [weightedLaplacian_apply, weightedLaplacian_apply, h.gradient_eq,
    (InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Derivatives of functions of temperate growth have temperate growth. -/
theorem hasTemperateGrowth_fderiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} (hg : g.HasTemperateGrowth) : (fderiv ℝ g).HasTemperateGrowth := by
  refine ⟨hg.1.fderiv_right (by simp), fun n => ?_⟩
  obtain ⟨k, C, hb⟩ := hg.2 (n + 1)
  exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using hb x⟩

/-! ### Integrability under exponential moments -/

variable (m : Measure E) [m.IsAddHaarMeasure]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [m.IsAddHaarMeasure] in
/-- Exponential tilts of a law with all exponential moments have all exponential moments. -/
theorem integrable_exp_mul_norm_expTilt {V : E → ℝ}
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) (z : E) (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) (expTilt (m.tilted (-V)) z) := by
    change Integrable (fun x => Real.exp (r * ‖x‖))
      ((m.tilted (-V)).tilted (fun x => ⟪z, x⟫))
    have hcont : Continuous (fun x : E => Real.exp ⟪z, x⟫) := by
      fun_prop
    have hbase : Integrable (fun x : E => Real.exp ⟪z, x⟫) (m.tilted (-V)) := by
      refine (hexp ‖z‖).mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall ?_)
      intro x
      calc
        ‖Real.exp ⟪z, x⟫‖ = Real.exp ⟪z, x⟫ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
        _ ≤ Real.exp (‖z‖ * ‖x‖) := by
          exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    rw [MeasureTheory.integrable_tilted_iff hbase]
    have hcont' :
        Continuous (fun x : E =>
          Real.exp ⟪z, x⟫ * Real.exp (r * ‖x‖)) := by
      fun_prop
    refine (hexp (‖z‖ + r)).mono' hcont'.aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro x
    have hpos :
        0 ≤ Real.exp ⟪z, x⟫ * Real.exp (r * ‖x‖) := by
      positivity
    calc
      ‖Real.exp ⟪z, x⟫ * Real.exp (r * ‖x‖)‖ =
          Real.exp ⟪z, x⟫ * Real.exp (r * ‖x‖) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      _ = Real.exp (⟪z, x⟫ + r * ‖x‖) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp ((‖z‖ + r) * ‖x‖) := by
        apply Real.exp_le_exp.mpr
        calc
          ⟪z, x⟫ + r * ‖x‖ ≤ ‖z‖ * ‖x‖ + r * ‖x‖ := by
            gcongr
            exact real_inner_le_norm z x
          _ = (‖z‖ + r) * ‖x‖ := by ring

/-! ### The integrated generator identity on temperate tests -/

section GeneratorGrowth

omit [MeasurableSpace E] [BorelSpace E]
private theorem growth_abs_weightedLaplacian_le (V g : E → ℝ) (x : E) :
    |weightedLaplacian V g x| ≤
      (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 g x‖ +
        ‖gradient V x‖ * ‖iteratedFDeriv ℝ 1 g x‖ := by
  rw [weightedLaplacian_apply]
  calc
    |Laplacian.laplacian g x - ⟪gradient V x, gradient g x⟫| ≤
        |Laplacian.laplacian g x| + |⟪gradient V x, gradient g x⟫| :=
      abs_sub _ _
    _ ≤ _ := by
      gcongr
      · exact abs_laplacian_le g x
      · simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using
          abs_real_inner_le_norm (gradient V x) (gradient g x)

private theorem growth_weightedLaplacian_bound {V g : E → ℝ}
    {CV C : ℝ} {kV k : ℕ} (hCV : 0 ≤ CV) (hC : 0 ≤ C)
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hg : ∀ x, ‖iteratedFDeriv ℝ 1 g x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 g x‖ ≤ C * (1 + ‖x‖) ^ k) (x : E) :
    |weightedLaplacian V g x| ≤
      ((Module.finrank ℝ E : ℝ) * C + CV * C) * (1 + ‖x‖) ^ (k + kV) := by
  have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
  calc
    |weightedLaplacian V g x| ≤
        (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      apply (growth_abs_weightedLaplacian_le V g x).trans
      gcongr
      · exact (hg x).2
      · exact hVg x
      · exact (hg x).1
    _ ≤
        (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ kV +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      have hm : (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) ≤
          (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ kV :=
        le_mul_of_one_le_right (by positivity) hp
      exact add_le_add_left hm _
    _ = _ := by rw [pow_add]; ring

end GeneratorGrowth

/-- `∫ ℒf dμ = 0` for `μ = m.tilted (-V)` with `V ∈ C¹`, `∇V` polynomially bounded and all
exponential moments, and `f ∈ C²` with `f`, `∇f`, `∇²f` polynomially bounded. -/
theorem integral_weightedLaplacian_eq_zero_of_growth {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : ContDiff ℝ 2 f) {C : ℝ} {k : ℕ}
    (hfg :
      ∀ x,
        |f x| ≤ C * (1 + ‖x‖) ^ k ∧
          ‖iteratedFDeriv ℝ 1 f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
            ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, weightedLaplacian V f x ∂(m.tilted (-V)) = 0 := by
  have hC : 0 ≤ C := by
    have h := (hfg 0).1
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hCV : 0 ≤ CV := by
    have h := hVg 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨C₁, h₁⟩ := norm_iteratedFDeriv_cutoff_le (E := E) 1
  obtain ⟨C₂, h₂⟩ := norm_iteratedFDeriv_cutoff_le (E := E) 2
  let K : ℝ := |C₁| + |C₂|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut (R : ℝ) (hR : 1 ≤ R) (x : E) :
    ‖iteratedFDeriv ℝ 1 (cutoff R) x‖ ≤ K ∧ ‖iteratedFDeriv ℝ 2 (cutoff R) x‖ ≤ K := by
    constructor
    · exact (h₁ R hR x).trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    · exact (h₂ R hR x).trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))
  let A : ℝ := (Module.finrank ℝ E : ℝ) * C + CV * C
  let B : ℝ := (Module.finrank ℝ E : ℝ) * K + CV * K
  let H : ℝ := A + 2 * K * C + C * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hLf (x : E) : |weightedLaplacian V f x| ≤ A * (1 + ‖x‖) ^ (k + kV) :=
    growth_weightedLaplacian_bound hCV hC hVg (fun x => (hfg x).2) x
  have hLcut (R : ℝ) (hR : 1 ≤ R) (x : E) :
    |weightedLaplacian V (cutoff R) x| ≤ B * (1 + ‖x‖) ^ kV := by
    simpa only [pow_zero, mul_one, zero_add] using
      growth_weightedLaplacian_bound hCV hK hVg (g := cutoff R) (k := 0)
        (fun y => by simpa using hcut R hR y) x
  let F : ℕ → E → ℝ := fun n => weightedLaplacian V (fun x => cutoff ((n : ℝ) + 1) x * f x)
  have hbound (n : ℕ) (x : E) : ‖F n x‖ ≤ H * (1 + ‖x‖) ^ (k + kV) := by
    have hR : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hc : ContDiff ℝ 2 (cutoff ((n : ℝ) + 1) : E → ℝ) :=
      (contDiff_cutoff (E := E) ((n : ℝ) + 1)).of_le
        (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)
    have hgcut : ‖gradient (cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hcut _ hR x).1
    have hgf : ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k := by
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hfg x).2.1
    have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
    have hp' : (1 + ‖x‖) ^ k ≤ (1 + ‖x‖) ^ (k + kV) := by
      rw [pow_add]
      exact le_mul_of_one_le_right (by positivity) hp
    dsimp only [F]
    rw [Real.norm_eq_abs, weightedLaplacian_mul V hc hf x, gamma_apply]
    rw [show ∀ a b c : ℝ, a + b + 2 * c = a + 2 * c + b from fun a b c => by ring]
    calc
      |cutoff ((n : ℝ) + 1) x * weightedLaplacian V f x +
                2 * ⟪gradient (cutoff ((n : ℝ) + 1)) x, gradient f x⟫ +
              f x * weightedLaplacian V (cutoff ((n : ℝ) + 1)) x| ≤
          |cutoff ((n : ℝ) + 1) x| * |weightedLaplacian V f x| +
              2 * (‖gradient (cutoff ((n : ℝ) + 1)) x‖ * ‖gradient f x‖) +
            |f x| * |weightedLaplacian V (cutoff ((n : ℝ) + 1)) x| := by
        calc
          _ ≤
              |cutoff ((n : ℝ) + 1) x * weightedLaplacian V f x| +
                  |2 * ⟪gradient (cutoff ((n : ℝ) + 1)) x, gradient f x⟫| +
                |f x * weightedLaplacian V (cutoff ((n : ℝ) + 1)) x| :=
            (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
          _ ≤ _ := by
            simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
            gcongr
            exact abs_real_inner_le_norm _ _
      _ ≤
          1 * (A * (1 + ‖x‖) ^ (k + kV)) + 2 * (K * (C * (1 + ‖x‖) ^ k)) +
            (C * (1 + ‖x‖) ^ k) * (B * (1 + ‖x‖) ^ kV) := by
        gcongr
        · exact abs_cutoff_le_one _ _
        · exact hLf x
        · exact (hfg x).1
        · exact hLcut _ hR x
      _ ≤
          1 * (A * (1 + ‖x‖) ^ (k + kV)) + 2 * (K * (C * (1 + ‖x‖) ^ (k + kV))) +
            (C * (1 + ‖x‖) ^ k) * (B * (1 + ‖x‖) ^ kV) := by
        exact
          add_le_add_left
            (add_le_add_right
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp' hC) hK) (by norm_num))
              _)
            _
      _ = H * (1 + ‖x‖) ^ (k + kV) := by dsimp [H]; rw [pow_add]; ring
  have hbi : Integrable (fun x : E => H * (1 + ‖x‖) ^ (k + kV)) (m.tilted (-V)) := by
    apply
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _ hexp (by fun_prop) (C := H)
        (k := k + kV)
    intro x
    rw [Real.norm_of_nonneg (by positivity)]
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) (m.tilted (-V)) :=
    (continuous_weightedLaplacian hV
        (((contDiff_cutoff (E := E) ((n : ℝ) + 1)).of_le
              (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).mul
          hf)).aestronglyMeasurable
  have hlim (x : E) : Tendsto (fun n => F n x) atTop (𝓝 (weightedLaplacian V f x)) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    symm
    apply weightedLaplacian_congr_of_eventuallyEq V
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    rw [cutoff_eq_one (by positivity) hy.le, one_mul]
  have ht :=
    tendsto_integral_of_dominated_convergence (fun x : E => H * (1 + ‖x‖) ^ (k + kV)) hmeas hbi
      (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hlim)
  have hz (n : ℕ) : (∫ x, F n x ∂(m.tilted (-V))) = 0 :=
    integral_weightedLaplacian_eq_zero m hV
      (((contDiff_cutoff (E := E) ((n : ℝ) + 1)).of_le
            (show (2 : ℕ∞ω) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).mul
        hf)
      ((hasCompactSupport_cutoff (by positivity)).mul_right)
  simp_rw [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem growth_test_bounds {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x,
      |f x| ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 1 f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 2
  refine ⟨k, C, hC, fun x => ⟨?_, hb 1 (by omega) x, hb 2 le_rfl x⟩⟩
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (by omega) x

/-- **BKL (48)** for `u ∈ 𝒜`: `F_{-ℒu}(z) = ⟪z, F_{∇u}(z)⟫` for every `z`. -/
theorem tiltAverage_neg_weightedLaplacian_of_hasTemperateGrowth {V f : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (z : E) :
    tiltAverage (m.tilted (-V)) (fun x => -weightedLaplacian V f x) z =
      ⟪z, tiltAverage (m.tilted (-V)) (gradient f) z⟫ := by
  obtain ⟨k, C, hC, hfg⟩ := growth_test_bounds hf
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hCV : 0 ≤ CV := by
    have h := hVg 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  unfold tiltAverage
  by_cases h : Integrable (fun x => Real.exp ((-V) x)) m
  · let W : E → ℝ := fun y => V y - ⟪z, y⟫
    have hlin : ContDiff ℝ 1 (fun y : E => ⟪z, y⟫) := (innerSL ℝ z).contDiff
    have hW : ContDiff ℝ 1 W := by simpa only [W] using hV.sub hlin
    have hz : expTilt (m.tilted (-V)) z = m.tilted (-W) := by
      simpa only [W] using expTilt_tilted m h z
    have hgrad : Integrable (gradient f) (expTilt (m.tilted (-V)) z) :=
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _
        (integrable_exp_mul_norm_expTilt m hexp z)
        (continuous_gradient_of_contDiff hf2 (by norm_num)).aestronglyMeasurable
        (fun x => by
          rw [norm_gradient_eq_norm_iteratedFDeriv_one]
          exact (hfg x).2.1)
    have hinner : Integrable (fun x => ⟪z, gradient f x⟫) (expTilt (m.tilted (-V)) z) :=
      (innerSL ℝ z).integrable_comp hgrad
    have hL : Integrable (fun x => weightedLaplacian V f x) (expTilt (m.tilted (-V)) z) :=
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _
        (integrable_exp_mul_norm_expTilt m hexp z)
        (continuous_weightedLaplacian hV hf2).aestronglyMeasurable
        (fun x => by
          rw [Real.norm_eq_abs]
          exact growth_weightedLaplacian_bound hCV hC hVg (fun y => (hfg y).2) x)
    have hzero : (∫ x, weightedLaplacian W f x ∂(expTilt (m.tilted (-V)) z)) = 0 := by
      calc
        (∫ x, weightedLaplacian W f x ∂(expTilt (m.tilted (-V)) z)) =
            ∫ x, weightedLaplacian W f x ∂(m.tilted (-W)) := by
          rw [hz]
        _ = 0 := by
          apply
            integral_weightedLaplacian_eq_zero_of_growth m hW (CV := CV + ‖z‖) (kV := kV) (C :=
              C) (k := k)
          · intro x
            have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
            rw [show gradient W x = gradient V x - z from
                gradient_sub_inner z x (hV.differentiable (by norm_num) x)]
            calc
              ‖gradient V x - z‖ ≤ ‖gradient V x‖ + ‖z‖ := norm_sub_le _ _
              _ ≤ CV * (1 + ‖x‖) ^ kV + ‖z‖ * (1 + ‖x‖) ^ kV := by
                exact add_le_add (hVg x) (le_mul_of_one_le_right (norm_nonneg _) hp)
              _ = (CV + ‖z‖) * (1 + ‖x‖) ^ kV := by ring
          · intro r
            rw [← hz]
            exact integrable_exp_mul_norm_expTilt m hexp z r
          · exact hf2
          · exact hfg
    exact integral_neg_weightedLaplacian_eq_inner hV z hgrad hL hzero
  · have hzero : m.tilted (-V) = 0 := tilted_of_not_integrable h
    have hz : expTilt (m.tilted (-V)) z = 0 := by
      unfold expTilt
      rw [hzero]
      exact tilted_zero_measure _
    rw [hz]
    simp

omit [CompleteSpace E] in
/-- Tilt averages of polynomially bounded measurable functions are smooth (finite nonzero measure
with all exponential moments). -/
theorem contDiff_tiltAverage_of_norm_le_pow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → F}
    (hf : AEStronglyMeasurable f μ) {M : ℝ} {k : ℕ} (hfb : ∀ x, ‖f x‖ ≤ M * (1 + ‖x‖) ^ k) :
    ContDiff ℝ ∞ (tiltAverage μ f) := by
    have hN :
        ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) :=
      contDiff_integral_exp_inner_smul μ hexp hf hfb
    have hD :
        ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
      simpa using
        (contDiff_integral_exp_inner_smul (μ := μ)
          (g := fun _ : E => (1 : ℝ)) (M := (1 : ℝ)) (k := 0)
          hexp
          (measurable_const.aestronglyMeasurable :
            AEStronglyMeasurable (fun _ : E => (1 : ℝ)) μ)
          (by
            intro x
            norm_num))
    have hDpos : ∀ z : E, 0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      intro z
      have hc : Continuous (fun x : E => Real.exp ⟪z, x⟫) :=
        Real.continuous_exp.comp (continuous_const.inner continuous_id)
      have hi : Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
        apply (hexp ‖z‖).mono' hc.aestronglyMeasurable
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
      have hnonneg : 0 ≤ᵐ[μ] (fun x => Real.exp ⟪z, x⟫) := by
        filter_upwards with x
        exact (Real.exp_pos _).le
      have hsupp :
          Function.support (fun x => Real.exp ⟪z, x⟫) = Set.univ := by
        ext x
        simp [Real.exp_ne_zero]
      have hμne : μ Set.univ ≠ 0 := by
        intro h
        apply (NeZero.ne μ)
        ext s
        simpa using measure_mono_null (Set.subset_univ s) h
      have hμ : 0 < μ Set.univ :=
        lt_of_le_of_ne zero_le (Ne.symm hμne)
      rw [integral_pos_iff_support_of_nonneg_ae hnonneg hi, hsupp]
      exact hμ
    have hform :
        tiltAverage μ f =
          fun z => (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
            (∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) := by
      funext z
      simp only [tiltAverage, expTilt, MeasureTheory.integral_tilted]
      calc
        (∫ x, (Real.exp ⟪z, x⟫ /
            ∫ y, Real.exp ⟪z, y⟫ ∂μ) • f x ∂μ) =
            ∫ x, (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ •
              (Real.exp ⟪z, x⟫ • f x) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          simp [div_eq_mul_inv, smul_smul, mul_comm]
        _ = (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ •
            ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ := by
          rw [integral_smul]
    rw [hform]
    exact (hD.inv (fun z => (hDpos z).ne')).smul hN

/-- **BKL Lemma 3.6, (50)**, for scalar `u ∈ 𝒜`: `T_{d+1}(-ℒu) = S_{d+1} T_d(∇u)`. -/
theorem taylorTensor_neg_weightedLaplacian_of_hasTemperateGrowth {V f : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (d : ℕ) :
    taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacian V f x) (d + 1) =
      symmetrizeML (appendInner (taylorTensor (m.tilted (-V)) (gradient f) d)) := by
  let μ : Measure E := m.tilted (-V)
  let G : E → E := tiltAverage μ (gradient f)
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hG : ContDiff ℝ ∞ G := by
    by_cases hi : Integrable (fun x => Real.exp ((-V) x)) m
    · let := isProbabilityMeasure_tilted hi
      obtain ⟨k, C, hC, hfg⟩ := growth_test_bounds hf
      apply contDiff_tiltAverage_of_norm_le_pow μ hexp
        (continuous_gradient_of_contDiff hf2 (by norm_num)).aestronglyMeasurable (M := C) (k := k)
      intro x
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]
      exact (hfg x).2.1
    · have hμ : m.tilted (-V) = 0 := tilted_of_not_integrable hi
      have hG0 : G = fun _ => (0 : E) := by
        funext x
        simp [G, μ, tiltAverage, expTilt, hμ]
      rw [hG0]
      exact contDiff_const
  have hEq :
      tiltAverage μ (fun x => -weightedLaplacian V f x) =
        fun w => ⟪w, G w⟫ := by
    funext w
    dsimp [G, μ]
    exact tiltAverage_neg_weightedLaplacian_of_hasTemperateGrowth m hV hVg hexp hf w
  exact taylorTensor_succ_of_eq_inner μ hG hEq d
/-- **BKL Lemma 3.6, (49)**, for scalar `u ∈ 𝒜`: `T_1(-ℒu)(h) = ⟪∫ ∇u dμ, h⟫`. -/
theorem taylorTensor_one_neg_weightedLaplacian_of_hasTemperateGrowth {V f : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (h : Fin 1 → E) :
    taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacian V f x) 1 h =
      ⟪∫ x, gradient f x ∂(m.tilted (-V)), h 0⟫ := by
    have h' :=
      taylorTensor_neg_weightedLaplacian_of_hasTemperateGrowth
        (m := m) hV hVg hexp hf 0
    have h'' := congrArg (fun T => T h) h'
    simpa [taylorTensor, symmetrizeML, appendInner,
      iteratedFDeriv_zero_apply, tiltAverage, expTilt, innerSL] using h''

end FunctionalInequalities.Analysis.BakryEmery
