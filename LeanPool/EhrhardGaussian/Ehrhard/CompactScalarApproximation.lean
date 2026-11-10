/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.CompactScalarBounds
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform smooth approximation preserving constancy outside a compact set -/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff Convolution

namespace EhrhardGaussian.Ehrhard

/-- A continuous function constant outside a compact set admits smooth uniform approximations with
the same tail constant. -/
theorem exists_smooth_compact_scalar_approximation {f : ℝ → ℝ} (hf : Continuous f)
    {c ε : ℝ} (hcompact : HasCompactSupport (fun y => f y - c)) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport (fun y => g y - c) ∧
      HasCompactSupport (deriv g) ∧ ∀ y, |g y - f y| < ε := by
  let F := fun y => f y - c
  have hF : Continuous F := hf.sub continuous_const
  have hUC : UniformContinuous F := hcompact.uniformContinuous_of_continuous hF
  obtain ⟨δ, hδ, hδbound⟩ := Metric.uniformContinuous_iff.mp hUC (ε / 2) (half_pos hε)
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let g₀ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  have hsmooth : ContDiff ℝ ∞ g₀ :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hF.locallyIntegrable
  have hcg₀ : HasCompactSupport g₀ :=
    φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcompact
  let g := fun y => g₀ y + c
  have hcg : HasCompactSupport (fun y => g y - c) := by
    simpa only [g, add_sub_cancel_right] using hcg₀
  have hsg : ContDiff ℝ ∞ g := hsmooth.add contDiff_const
  refine ⟨g, hsg, hcg, hasCompactSupport_deriv_of_sub_const
    ((hsg.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).differentiable_one) hcg, ?_⟩
  intro y
  have hdist : dist (g₀ y) (F y) ≤ ε / 2 :=
    φ.dist_normed_convolution_le hF.aestronglyMeasurable (fun z hz => (hδbound hz).le)
  calc
    |g y - f y| = dist (g₀ y) (F y) := by rw [Real.dist_eq]; congr 1; dsimp only [g, F]; ring
    _ ≤ ε / 2 := hdist
    _ < ε := half_lt_self hε

end EhrhardGaussian.Ehrhard

end
