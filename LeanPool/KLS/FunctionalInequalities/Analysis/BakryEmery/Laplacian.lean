/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Calculus
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The weighted Laplacian

The classical diffusion expression, continuity, compact support and finite-measure Lp membership.
No integration-by-parts or closed-generator identification is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- The weighted Laplacian `ℒ f = Δ f - ⟪∇U, ∇f⟫` of the potential `U`, as a pointwise
differential expression on classical functions. It is the diffusion-generator convention: the
nonnegative operator of the heat semigroup is `-ℒ`. -/
def weightedLaplacian (U f : E → ℝ) (x : E) : ℝ :=
  Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫

theorem weightedLaplacian_apply (U f : E → ℝ) (x : E) :
    weightedLaplacian U f x = Laplacian.laplacian f x - ⟪gradient U x, gradient f x⟫ := rfl

/-- The weighted Laplacian of a `C²` function for a `C¹` potential is continuous. -/
theorem continuous_weightedLaplacian {U f : E → ℝ} (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 2 f) :
    Continuous (weightedLaplacian U f) :=
  (continuous_laplacian hf).sub
    ((continuous_gradient hU).inner (continuous_gradient (hf.of_le (by norm_num))))

/-- Regularity of the weighted Laplacian: a `C^{n+1}` potential and `C^{n+2}` data give a `C^n`
weighted Laplacian. -/
theorem contDiff_weightedLaplacian {n p q : WithTop ℕ∞} {U f : E → ℝ} (hU : ContDiff ℝ p U)
    (hf : ContDiff ℝ q f) (hp : n + 1 ≤ p) (hq : n + 2 ≤ q) :
    ContDiff ℝ n (weightedLaplacian U f) := by
  have hnq : n + 1 ≤ q :=
    le_trans (by gcongr; norm_num : n + (1 : WithTop ℕ∞) ≤ n + 2) hq
  exact ContDiff.sub (contDiff_laplacian hf hq)
    (ContDiff.inner ℝ (contDiff_gradient hU hp) (contDiff_gradient hf hnq))

/-- **The weighted Laplacian is local**: it vanishes at every point outside the closed support of
its argument, because both the gradient and the second derivative do. The potential is
unrestricted. -/
theorem weightedLaplacian_eq_zero_of_notMem_tsupport (U : E → ℝ) {f : E → ℝ} {x : E}
    (hx : x ∉ tsupport f) : weightedLaplacian U f x = 0 := by
  have h1 : fderiv ℝ f x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset (𝕜 := ℝ) h)
  have h2 : fderiv ℝ (fderiv ℝ f) x = 0 := by
    by_contra h
    exact hx (tsupport_fderiv_subset (𝕜 := ℝ) (support_fderiv_subset (𝕜 := ℝ) h))
  have hgrad : gradient f x = 0 := by
    rw [gradient, h1, map_zero]
  have hlap : Laplacian.laplacian f x = 0 := by
    rw [laplacian_eq_sum_fderiv_fderiv, h2]
    simp
  rw [weightedLaplacian_apply, hlap, hgrad, inner_zero_right, sub_zero]

/-- The weighted Laplacian of a compactly supported function has compact support. -/
theorem hasCompactSupport_weightedLaplacian (U : E → ℝ) {f : E → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (weightedLaplacian U f) := by
  refine (hasCompactSupport_laplacian hfc).sub ?_
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [h0]

section Integrable

variable [MeasurableSpace E] [BorelSpace E]

/-- The weighted Laplacian of a `C²` compactly supported function lies in every `L^p` of a finite
measure; the potential need only be `C¹`. -/
theorem memLp_weightedLaplacian {μ : Measure E} [IsFiniteMeasure μ] {U f : E → ℝ}
    (hU : ContDiff ℝ 1 U) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (p : ENNReal) :
    MemLp (weightedLaplacian U f) p μ :=
  (continuous_weightedLaplacian hU hf).memLp_of_hasCompactSupport
    (hasCompactSupport_weightedLaplacian U hfc)

end Integrable

end FunctionalInequalities.Analysis.BakryEmery
