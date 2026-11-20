/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryLangevinLocal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryConvexLift
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathContinuousNoisePicard
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The actual locally regular Langevin drift

Local existence is proved for the literal Euclidean gradient drift and
continuous additive driving paths. Global existence and the entropy theorem
are separate subsequent obligations.
-/

@[expose] public section

open Set Metric
open scoped ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The literal unit-diffusion gradient Langevin drift. -/
def bakryEmeryLangevinDrift (W : E → ℝ) (x : E) : E :=
  -gradient W x

omit [FiniteDimensional ℝ E] in
/-- A C² confinement supplies a C¹ Langevin drift internally. -/
theorem bakryEmeryLangevinDrift_contDiffAt (W : E → ℝ) (x : E)
    (hW : ContDiffAt ℝ 2 W x) :
    ContDiffAt ℝ 1 (bakryEmeryLangevinDrift W) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ W) x :=
    (show ContDiffAt ℝ (1 + 1) W x from hW).fderiv_right_succ
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
      hd).neg

omit [FiniteDimensional ℝ E] in
/-- The local Picard coefficient is derived from actual C² confinement. -/
theorem bakryEmeryLangevinDrift_local_lipschitz (W : E → ℝ) (x : E)
    (hW : ContDiffAt ℝ 2 W x) :
    ∃ K : ℝ≥0, ∃ s ∈ nhds x, LipschitzOnWith K (bakryEmeryLangevinDrift W) s :=
  (bakryEmeryLangevinDrift_contDiffAt W x hW).exists_lipschitzOnWith

/-- Actual local solution for arbitrary continuous additive noise, from the
locally C¹ gradient drift. This does not assume a diffusion solution. -/
theorem bakryEmeryLangevin_continuous_noise_local (W : E → ℝ) (z : E)
    (hW : ContDiffAt ℝ 2 W z) (N : ℝ → E) (hN : Continuous N) (hN0 : N 0 = 0) :
    ∃ Y : ℝ → E, Y 0 = z ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt Y (bakryEmeryLangevinDrift W (Y t + N t)) t := by
  obtain ⟨K, s, hs, hb⟩ := bakryEmeryLangevinDrift_local_lipschitz W z hW
  obtain ⟨g, hg, heq⟩ := hb.extend_finite_dimension
  obtain ⟨Y, hY0, ε, hε, hY⟩ :=
    drivenContinuousNoise_lipschitz_local_correction g _ hg N hN z
  have hYcont : ContinuousAt Y 0 := (hY 0 (by constructor <;> linarith)).continuousAt
  have hXcont : ContinuousAt (fun t => Y t + N t) 0 := hYcont.add hN.continuousAt
  have hX0 : Y 0 + N 0 = z := by rw [hY0, hN0, add_zero]
  have hev : ∀ᶠ t in nhds 0, Y t + N t ∈ s := hXcont.eventually (by
    dsimp only
    rw [hX0]
    exact hs)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨Y, hY0, min ε δ, lt_min hε hδ, ?_⟩
  intro t ht
  have hte : t ∈ Ioo (-ε) ε := ⟨by linarith [min_le_left ε δ, ht.1],
    ht.2.trans_le (min_le_left ε δ)⟩
  have hts : Y t + N t ∈ s := hδs (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [min_le_right ε δ, ht.1], ht.2.trans_le (min_le_right ε δ)⟩)
  rw [heq hts]
  exact hY t hte

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The lifted potential is C² away from the block origin, derived by the
ordinary norm chain rule. Smoothness at the origin needs a separate radial
extension argument. -/
theorem bakryEmeryEuclideanLiftPotential_contDiffAt_nonzero
    (n : ℕ) {V : Potential} (hV : ContDiff ℝ 2 V) (x : E) (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (bakryEmeryEuclideanLiftPotential n V) x := by
  have hn : ContDiffAt ℝ 2 (norm : E → ℝ) x := contDiffAt_norm ℝ hx
  exact contDiffAt_const.mul (hV.contDiffAt.comp x
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x hn))

end
end GinibrePoincare
