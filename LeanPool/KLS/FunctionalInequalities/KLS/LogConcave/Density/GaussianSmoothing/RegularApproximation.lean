/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Regular
public import LeanPool.KLS.FunctionalInequalities.Probability.QuadraticTilt
public import LeanPool.KLS.FunctionalInequalities.Analysis.DiagonalSelector
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The regular approximation: joint Gaussian-then-quadratic diagonal

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): every probability law with a Borell
density and finite second moment is approximated by the laws of regular potentials
`V_{n+1} + δ_k/2‖·‖²` (Gaussian smoothing of variance `1/(2(n+1))`, then the quadratic tilt of rate
`δ_k = 1/(k+1)`), with curvature bounds `δ_k ≤ ∇² ≤ 2(n+1) + δ_k`. Along a diagonal `k n ≥ n`
selected in the metrizable product of the weak topology with the statistics, the laws converge
weakly and their means, raw second moments and covariance operators converge to those of the
law. Convergence of whitened laws and the limit of the Poincaré constants are separate (the
conditional transfer is in `KLS/LogConcave/Regular/Poincare.lean`).
-/

@[expose] public section

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis

noncomputable section

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The quadratic-tilt rates `δ_k = 1/(k+1)`. -/
def tiltRate (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem tiltRate_pos (k : ℕ) : 0 < tiltRate k := by unfold tiltRate; positivity

theorem tiltRate_tendsto_zero : Tendsto tiltRate atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- `δ_{k n} ≤ δ_n` when `k n ≥ n`. -/
theorem selected_tiltRate_le {k : ℕ → ℕ} (hk : ∀ n, n ≤ k n) (n : ℕ) :
    tiltRate (k n) ≤ tiltRate n := by
  unfold tiltRate
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hcast : (n : ℝ) ≤ (k n : ℝ) := by exact_mod_cast hk n
  linarith

theorem selected_tiltRate_tendsto_zero {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) := tiltRate_tendsto_zero.comp hk

/-- The Gaussian smoothings `μ * γ_{n+1}` as probability laws. -/
def gaussianSeq (μ : ProbabilityMeasure E) (n : ℕ) : ProbabilityMeasure E :=
  smoothedProbabilityLaw μ ((n : ℝ) + 1) (by positivity)

/-- Mean, raw second moment and covariance operator of a law. -/
def statistics (ν : ProbabilityMeasure E) : E × (ℝ × (E →L[ℝ] E)) :=
  (∫ y, y ∂(ν : Measure E), ∫ y, ‖y‖ ^ 2 ∂(ν : Measure E), Covariance.operator (ν : Measure E))

/-- Joint convergence of the smoothings and their statistics to those of `μ`. -/
theorem gaussian_joint_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    Tendsto (fun n : ℕ => (gaussianSeq μ n, statistics (gaussianSeq μ n)))
      atTop (𝓝 (μ, statistics μ)) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hw := smoothedProbabilityLaw_tendsto hρ
  have hm := (smoothedLaw_mean_tendsto (μ : Measure E) hμ2).comp hn
  have hsecond := (smoothedLaw_norm_sq_tendsto (μ : Measure E) hμ2).comp hn
  have hcov := (smoothedLaw_covariance_operator_tendsto (μ : Measure E) hμ2).comp hn
  exact hw.prodMk_nhds (hm.prodMk_nhds (hsecond.prodMk_nhds hcov))

/-- The two-step laws: Gaussian smoothing `n`, then quadratic tilt with tiltRate `δ_k`. -/
def rowLaw (μ : ProbabilityMeasure E) (n k : ℕ) : ProbabilityMeasure E :=
  Probability.quadraticTiltLaw (gaussianSeq μ n) (tiltRate k) (tiltRate_pos k).le

/-- For fixed `n`, the row converges (law and statistics) to the smoothing as `k → ∞`. -/
theorem row_joint_tendsto (μ : ProbabilityMeasure E) (hμ2 : MemLp id 2 (μ : Measure E)) (n : ℕ) :
    Tendsto (fun k : ℕ => (rowLaw μ n k, statistics (rowLaw μ n k)))
      atTop (𝓝 (gaussianSeq μ n, statistics (gaussianSeq μ n))) := by
  let ν : ProbabilityMeasure E := gaussianSeq μ n
  have hν2 : MemLp id 2 (ν : Measure E) :=
    smoothedLaw_memLp_two (μ : Measure E) hμ2 (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hr : Tendsto tiltRate atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tiltRate_tendsto_zero, Eventually.of_forall tiltRate_pos⟩
  have hw := Probability.quadraticTiltLaw_tendsto ν tiltRate tiltRate_pos tiltRate_tendsto_zero
  have hm := (Probability.integral_id_quadraticTilt_tendsto (ν : Measure E)
    (hν2.integrable one_le_two)).comp hr
  have hnorm : Integrable (fun y : E => ‖y‖ ^ 2) (ν : Measure E) :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).1 hν2
  have hsecond := (Probability.integral_norm_sq_quadraticTilt_tendsto (ν : Measure E) hnorm).comp hr
  have hcov := (Probability.covariance_quadraticTilt_tendsto ν hν2).comp hr
  exact hw.prodMk_nhds (hm.prodMk_nhds (hsecond.prodMk_nhds hcov))

/-- A diagonal `k n ≥ n` along which the two-step laws and their statistics converge to `μ`. -/
theorem exists_diagonal_tendsto {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ Tendsto k atTop atTop ∧
      (∀ n, 0 < tiltRate (k n)) ∧ Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => (rowLaw μ n (k n), statistics (rowLaw μ n (k n))))
        atTop (𝓝 (μ, statistics μ)) := by
  let X := ProbabilityMeasure E × (E × (ℝ × (E →L[ℝ] E)))
  let : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  obtain ⟨k, hkl, hk, hdiag⟩ := Analysis.exists_metric_diagonal
    (fun n j => (rowLaw μ n j, statistics (rowLaw μ n j)))
    (fun n => (gaussianSeq μ n, statistics (gaussianSeq μ n)))
    (μ, statistics μ) (row_joint_tendsto μ hμ2) (gaussian_joint_tendsto hρ hμ2)
  exact ⟨k, hkl, hk, fun n => tiltRate_pos (k n), selected_tiltRate_tendsto_zero hk, hdiag⟩

/-- The diagonal with the four limits (law, mean, raw second moment, covariance) exposed. -/
theorem exists_diagonal_limits {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n => rowLaw μ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  obtain ⟨k, hkl, _hk, hpos, hδ, hdiag⟩ := exists_diagonal_tendsto hρ hμ2
  exact ⟨k, hkl, hpos, hδ, hdiag.fst_nhds, hdiag.snd_nhds.fst_nhds,
    hdiag.snd_nhds.snd_nhds.fst_nhds, hdiag.snd_nhds.snd_nhds.snd_nhds⟩

/-- Each two-step law is the law of the produced regular potential, with positive constants. -/
theorem rowLaw_regular {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (n k : ℕ) :
    let hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    let hδ := tiltRate_pos k
    let hV := regularPotential_quadraticPotential hρ hs hδ
    (0 < tiltRate k) ∧ (0 < 2 * ((n : ℝ) + 1) + tiltRate k) ∧
      hV.law = rowLaw μ n k := by
  dsimp only
  refine ⟨tiltRate_pos k, two_mul_add_pos (by positivity) (tiltRate_pos k), ?_⟩
  exact regularLaw_eq_quadraticTilt hρ (by positivity) (tiltRate_pos k)

/-- **Regular approximation** (BKL Section 2, p. 5): a law with a Borell density and finite second
moment is the weak limit of laws of regular potentials `V_{n+1} + δ/2‖·‖²` with curvature bounds
`δ ≤ ∇² ≤ 2(n+1) + δ`, with means, raw second moments and covariance operators converging too.
No whitened-sequence convergence is asserted. -/
theorem exists_regular_approximation_limits
    {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential ρ ((n : ℝ) + 1) (tiltRate (k n))) (tiltRate (k n))
        (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => rowLaw μ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (rowLaw μ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  obtain ⟨k, hkl, hpos, hδ, hw, hm, hsecond, hcov⟩ := exists_diagonal_limits hρ hμ2
  exact ⟨k, hkl, hpos, hδ, fun n => regularPotential_quadraticPotential hρ (by positivity) (hpos n),
    fun n => two_mul_add_pos (by positivity) (hpos n), hw, hm, hsecond, hcov⟩

/-- The law of the produced regular potential at smoothing `n+1` and tilt tiltRate `δ_k`. -/
def regularSeq {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (n k : ℕ) : ProbabilityMeasure E :=
  (regularPotential_quadraticPotential hρ
    (by positivity : (0 : ℝ) < (n : ℝ) + 1) (tiltRate_pos k)).law

/-- It equals the two-step law. -/
theorem regularSeq_eq_rowLaw {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (n k : ℕ) :
    regularSeq hρ n k = rowLaw μ n k :=
  regularLaw_eq_quadraticTilt hρ (by positivity) (tiltRate_pos k)

/-- The regular approximation stated for `regularSeq`. -/
theorem exists_regularSeq_limits
    {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity (μ : Measure E) volume ρ) (hμ2 : MemLp id 2 (μ : Measure E)) :
    ∃ k : ℕ → ℕ, (∀ n, n ≤ k n) ∧ (∀ n, 0 < tiltRate (k n)) ∧
      Tendsto (fun n => tiltRate (k n)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ n : ℕ, KLS.RegularPotential
        (quadraticPotential ρ ((n : ℝ) + 1) (tiltRate (k n))) (tiltRate (k n))
        (2 * ((n : ℝ) + 1) + tiltRate (k n))) ∧
      (∀ n : ℕ, 0 < 2 * ((n : ℝ) + 1) + tiltRate (k n)) ∧
      Tendsto (fun n => regularSeq hρ n (k n)) atTop (𝓝 μ) ∧
      Tendsto (fun n => ∫ y : E, y ∂(regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, y ∂(μ : Measure E))) ∧
      Tendsto (fun n => ∫ y : E, ‖y‖ ^ 2 ∂(regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (∫ y : E, ‖y‖ ^ 2 ∂(μ : Measure E))) ∧
      Tendsto (fun n => Covariance.operator (regularSeq hρ n (k n) : Measure E)) atTop
        (𝓝 (Covariance.operator (μ : Measure E))) := by
  simpa only [regularSeq_eq_rowLaw] using
    exists_regular_approximation_limits hρ hμ2

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

end
