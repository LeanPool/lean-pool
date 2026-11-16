/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Poincare
public import LeanPool.KLS.FunctionalInequalities.Poincare.SmoothTest.WeakLimit

/-!
# Weak limits of Poincaré bounds for log-concave laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): a Poincaré inequality that holds along a
weakly convergent sequence of laws with converging constants passes to a log-concave limit law, in
the literature (local-slope) constant. This is the transfer step of the regular approximation; the
approximating laws themselves (Gaussian smoothing and quadratic tilt) are constructed elsewhere.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.KLS.LogConcave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- **Weak-limit transfer of the Poincaré bound to the literature constant of a log-concave law**
(BKL arXiv:2610.05474v1, Section 2, p. 5): if `μ_j → μ` weakly, each `μ_j` satisfies the smooth-test
Poincaré bound with constant `C_j`, and `C_j → C`, then the log-concave limit `μ` has literature
constant at most `C`. The smooth-test bound passes to the limit on compactly supported smooth tests
(`Poincare.SmoothTest.variance_le_mul_energy_of_tendsto`), extends to all admissible tests by the
cutoff argument (`Poincare.SmoothTest.Holds.of_compactSupport`), and the smooth-test constant equals
the literature constant for log-concave laws. -/
theorem localSlope_constant_le_of_tendsto (μs : ℕ → ProbabilityMeasure E)
    (μ : ProbabilityMeasure E) (hμ : LogConcave μ) (Cseq : ℕ → NNReal) (C : NNReal)
    (hlim : Tendsto μs atTop (𝓝 μ)) (hClim : Tendsto Cseq atTop (𝓝 C))
    (hbound : ∀ j, Poincare.SmoothTest.Holds (μs j : Measure E) (Cseq j : ℝ)) :
    Poincare.LocalSlope.Intrinsic.optimalConstant μ ≤ (C : ENNReal) := by
    rw [← smoothTest_constant_eq_localSlope hμ]
    refine Poincare.SmoothTest.constant_le
      (Poincare.SmoothTest.Holds.of_compactSupport (C := (C : ℝ)) C.2 ?_)
    intro f hf hc
    have hClim' : Tendsto (fun j => (Cseq j : ℝ)) atTop (𝓝 (C : ℝ)) :=
      (NNReal.continuous_coe.tendsto C).comp hClim
    have hadm_j : ∀ j, Poincare.SmoothTest.Admissible (μs j : Measure E) f :=
      fun j =>
        Poincare.SmoothTest.Admissible.of_contDiff_hasCompactSupport hf.smooth' hc
    exact
      Poincare.SmoothTest.variance_le_mul_energy_of_tendsto hlim hClim' hf.smooth' hc
        (fun j => (hbound j).variance_le (hadm_j j))

end FunctionalInequalities.KLS.LogConcave
