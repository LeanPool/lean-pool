/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Conditioning
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.BallConditioning
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.CompactReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.IsotropicReduction
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.RegularApproximation
public import LeanPool.KLS.FunctionalInequalities.KLS.Letwin.Approximation

/-!
# Reduction of the compact Letwin bound to the regular class

`letwinCompactBound_of_regularClass`: if Letwin's quadratic-form bound holds for every isotropic law
with density
`1_K e^{-W}` (K a compact convex body, W smooth and κ-strongly convex), it holds for every compactly
supported isotropic
log-concave law, i.e. `LetwinCompactBound` (Letwin arXiv:2607.24164v1, Lemma A.1 approximation by
Gaussian smoothing,
ball conditioning and whitening).
The approximants come from `exists_regularClass_seq_of_compact` (`KLS/Letwin/Approximation.lean`);
the bound passes
to the limit by `letwinQuadraticBound_of_tendsto_moments`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/--
**Reduction of the compact Letwin bound to Letwin's regular class** (Letwin arXiv:2607.24164v1,
Lemma A.1): if every isotropic law `1_K e^{−W} dx` with `K` compact convex with nonempty interior
and `W` smooth and
uniformly convex satisfies Letwin's quadratic bound, then so does every compactly supported
isotropic log-concave law
in positive dimension (`LetwinCompactBound`). -/
theorem letwinCompactBound_of_regularClass
    (h :
      ∀ (n : ℕ),
        0 < n →
          ∀ (K : Set (EuclideanSpace ℝ (Fin n))) (W : EuclideanSpace ℝ (Fin n) → ℝ) (κ : ℝ),
            0 < κ →
              IsCompact K →
                Convex ℝ K →
                  (interior K).Nonempty →
                    ContDiff ℝ ∞ W →
                      ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2) →
                        ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
                          (μ : Measure (EuclideanSpace ℝ (Fin n))) =
                              (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
                                (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
                            KLS.Isotropic μ →
                              LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    LetwinCompactBound := by
  intro n hn μ hLC hiso hcompact
  have hmem (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hν : KLS.LogConcave ν) :
    MemLp id 4 (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_norm_rpow_iff (p := 4) continuous_id.aestronglyMeasurable (by norm_num)
          (by norm_num)).mp
      (by simpa using hν.integrable_norm_pow 4)
  obtain ⟨ζ, hζ, hmom⟩ := exists_regularClass_seq_of_compact μ hLC hiso hcompact
  have hζLC (j : ℕ) : KLS.LogConcave (ζ j) := by
    obtain ⟨-, K, W, κ, hκ, hK, hKc, -, hW, hWc, heq⟩ := hζ j
    exact logConcave_of_eq_regularClass (ζ j) hK.isClosed hKc hW.continuous hκ hWc heq
  refine
    letwinQuadraticBound_of_tendsto_moments
      (fun j => (ζ j : Measure (EuclideanSpace ℝ (Fin n))))
      (μ : Measure (EuclideanSpace ℝ (Fin n))) (fun j => hmem (ζ j) (hζLC j)) (hmem μ hLC) hmom
      fun j => ?_
  obtain ⟨hisoj, K, W, κ, hκ, hK, hKc, hKint, hW, hWc, heq⟩ := hζ j
  exact h n hn K W κ hκ hK hKc hKint hW hWc (ζ j) heq hisoj

end FunctionalInequalities.KLS.LogConcave.Suspension
