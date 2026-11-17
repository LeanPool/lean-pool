/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Growth
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import LeanPool.KLS.FunctionalInequalities.Probability.QuadraticTilt

/-!
# The regular approximation produces regular potentials

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): smoothing a law with a Borell density by
the Gaussian of variance `ε = 1/(2s)` and then tilting by `e^{-δ‖x‖²/2}` yields the law of the
potential `V_s + δ/2‖·‖²`, which is regular in the sense of (12): smooth with polynomial growth of
all
derivatives (`Growth`), convex, and `δ · Id ≤ ∇² ≤ (2s + δ) · Id` (`Hessian`). The two-step law is
identified exactly with `Probability.quadraticTiltLaw (smoothedProbabilityLaw μ s) δ` and is
log-concave. The approximation sequence, covariance normalization and the passage to the limit are
not treated here.
-/

@[expose] public section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

open FunctionalInequalities.Probability.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- The quadratic tilt of the smoothed law is the law of the potential `V_s + δ/2‖·‖²`. -/
theorem quadraticTilt_smoothedLaw_eq_tilted {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) (δ : ℝ) :
    (smoothedLaw μ s).tilted (fun y => -(δ / 2) * ‖y‖ ^ 2) =
      (volume : Measure E).tilted (-(fun y => potential ρ s y + δ / 2 * ‖y‖ ^ 2)) := by
  rw [smoothedLaw_eq_tilted_potential hρ hs]
  have hi : Integrable (fun y => Real.exp ((-potential ρ s) y)) (volume : Measure E) := by
    convert integrable_normalizedDensity hρ hs using 1
    funext y
    simp [potential, Real.exp_log (normalizedDensity_pos hρ hs y)]
  rw [MeasureTheory.tilted_tilted hi]
  congr 1
  funext y
  simp
  ring


/--
The potential `V_s + δ/2‖·‖²` of the Gaussian smoothing followed by the quadratic tilt (BKL (12)).
-/
noncomputable def quadraticPotential (ρ : E → ℝ) (s δ : ℝ) : E → ℝ := fun y =>
  potential ρ s y + δ / 2 * ‖y‖ ^ 2

/--
**The regular approximation produces a regular potential** (BKL Section 2, p. 5): for a probability
law with a Borell density, `s > 0`, `δ > 0`, the potential `V_s + δ/2‖·‖²` is regular with curvature
bounds `δ ≤ ∇² ≤ 2s + δ` (`ε = 1/(2s)`). -/
theorem regularPotential_quadraticPotential {μ : Measure E} [IsProbabilityMeasure μ] {ρ : E → ℝ}
    (hρ : IsBorellDensity μ volume ρ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    RegularPotential (quadraticPotential ρ s δ) δ (2 * s + δ) := by
  exact
    RegularPotential.of_convexOn_hasTemperateGrowth (potential_hasTemperateGrowth hρ hs)
      (potential_convex hρ hs) hδ (bilinearIteratedFDerivTwo_potential_le hρ hs)

/-- `2s + δ > 0`. -/
theorem two_mul_add_pos {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) : 0 < 2 * s + δ := by
  linarith

/--
The law of the produced regular potential is the two-step law: Gaussian smoothing, then quadratic
tilt. -/
theorem regularLaw_eq_quadraticTilt {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : IsBorellDensity (μ : Measure E) volume ρ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (regularPotential_quadraticPotential hρ hs hδ).law =
      Probability.quadraticTiltLaw (smoothedProbabilityLaw μ s hs) δ hδ.le := by
  apply Subtype.ext
  change
    (volume : Measure E).tilted (-quadraticPotential ρ s δ) =
      (smoothedLaw (μ : Measure E) s).tilted (fun y => -(δ / 2) * ‖y‖ ^ 2)
  exact (quadraticTilt_smoothedLaw_eq_tilted hρ hs δ).symm

/-- The two-step law is log-concave. -/
theorem quadraticTilt_logConcave {μ : ProbabilityMeasure E} {ρ : E → ℝ}
    (hρ : IsBorellDensity (μ : Measure E) volume ρ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    KLS.LogConcave (Probability.quadraticTiltLaw (smoothedProbabilityLaw μ s hs) δ hδ.le) := by
  rw [← regularLaw_eq_quadraticTilt hρ hs hδ]
  exact (regularPotential_quadraticPotential hρ hs hδ).logConcave_law


end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
