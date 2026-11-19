/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoPathMesh.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoLocalPartition
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticOUPast
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticVariation

/-!
# Finite dimensional Ito path mesh

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `itoUniformPathMesh_increment_le`, `itoUniformPathMesh_tendsto`.
-/

@[expose] public section

open Filter Metric
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

/-- The largest increment norm `‖z tᵢ₊₁ - z tᵢ‖` of a path `z` over the uniform partition of
`[0, T]` into `n + 1` steps. -/
def itoUniformPathMesh (z : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (n+1) =>
    ‖z (ginibreUniformBrownianTime T n (i.val+1)) - z (ginibreUniformBrownianTime T n i)‖)

theorem itoUniformPathMesh_nonneg (z : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) :
    0 ≤ itoUniformPathMesh z T n := by
  exact (norm_nonneg _).trans (Finset.le_sup' (f := fun i : Fin (n+1) =>
    ‖z (ginibreUniformBrownianTime T n (i.val+1)) - z (ginibreUniformBrownianTime T n i)‖)
      (Finset.mem_univ (0 : Fin (n+1))))

theorem itoUniformPathMesh_increment_le (z : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) (i : Fin (n + 1)) :
    ‖z (ginibreUniformBrownianTime T n (i.val+1)) - z (ginibreUniformBrownianTime T n i)‖ ≤
      itoUniformPathMesh z T n := by
  unfold itoUniformPathMesh
  exact Finset.le_sup' (f := fun i : Fin (n+1) =>
    ‖z (ginibreUniformBrownianTime T n (i.val+1)) - z (ginibreUniformBrownianTime T n i)‖)
      (Finset.mem_univ i)

/-- Continuity of an actual path makes its actual uniform-partition increment mesh vanish. -/
theorem itoUniformPathMesh_tendsto (z : ℝ≥0 → E) (T : ℝ≥0)
    (hz : ContinuousOn z (Set.Icc 0 T)) :
    Tendsto (itoUniformPathMesh z T) atTop (𝓝 0) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hz
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have hlim : Tendsto (fun n : ℕ => (T : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T : ℝ)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (itoUniformPathMesh_nonneg z T n)]
  unfold itoUniformPathMesh
  apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
  intro i hi
  have ha : ginibreUniformBrownianTime T n (i.val+1) ∈ Set.Icc 0 T :=
    ⟨bot_le, ginibreUniformBrownianTime_le_end T n _ (Nat.succ_le_of_lt i.is_lt)⟩
  have hb : ginibreUniformBrownianTime T n i ∈ Set.Icc 0 T :=
    ⟨bot_le, ginibreUniformBrownianTime_le_end T n _ (Nat.le_of_lt i.is_lt)⟩
  have hd : dist (ginibreUniformBrownianTime T n (i.val+1))
      (ginibreUniformBrownianTime T n i) < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show
      (ginibreUniformBrownianTime T n i : ℝ) ≤ ginibreUniformBrownianTime T n (i.val+1) from
        ginibreUniformBrownianTime_mono T n (Nat.le_succ i.val))),
      ginibreUniformBrownianTime_coe, ginibreUniformBrownianTime_coe,
      ginibreUniformTime_increment]
    exact hn
  simpa only [dist_eq_norm] using hu _ ha _ hb hd

end
end GinibrePoincare
