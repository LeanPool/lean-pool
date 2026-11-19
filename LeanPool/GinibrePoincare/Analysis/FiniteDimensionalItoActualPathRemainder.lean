/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/FiniteDimensionalItoActualPathRemainder.lean.
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

public import LeanPool.GinibrePoincare.Analysis.FiniteDimensionalItoPathMesh

/-! # Taylor remainder sums along a continuous path

On a finite horizon, the path image is compact and contained in its open
C² domain. The uniform local Taylor estimate and vanishing path mesh bound
the total remainder by an arbitrarily small factor times the sum of squared
increments.

The first theorem assumes those quadratic sums are bounded and concludes
that the unnormalized remainder tends to zero. The next two normalize by
the quadratic sum, or by one plus that sum, and require no such bound. In
the zero-denominator branch the quotient is Lean's totalized zero quotient;
otherwise the positive denominator cancels the quadratic factor in the
error bound. The `1 + quadratic` version avoids this branch and feeds the
convergence-in-measure estimates for stochastic remainder terms. -/

@[expose] public section

open Filter Metric
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- The quadratic-variation sum `∑ ‖z tᵢ₊₁ - z tᵢ‖²` of a path `z` along the uniform partition
of `[0, T]` into `n + 1` steps. -/
def itoActualPathQuadraticSum (z : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (n+1), ‖z (ginibreUniformBrownianTime T n (i.val+1)) -
    z (ginibreUniformBrownianTime T n i)‖^2

/-- The sum of the second-order Taylor remainders of `f` along the increments of the path `z`
over the uniform partition of `[0, T]` into `n + 1` steps. -/
def itoActualPathTaylorRemainderSum (f : E → ℝ) (z : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (n+1), itoTaylorRemainder f (z (ginibreUniformBrownianTime T n i))
    (z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i))

/-- Actual continuous paths remaining in an open C² domain have vanishing
uniform-partition Taylor remainder whenever their actual quadratic sums are bounded. -/
theorem itoActualPathRemainder_tendsto (f : E → ℝ) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (z : ℝ≥0 → E) (T : ℝ≥0)
    (hz : ContinuousOn z (Set.Icc 0 T)) (hzU : ∀ t ∈ Set.Icc 0 T, z t ∈ U)
    (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ n, ∑ i : Fin (n + 1),
      ‖z (ginibreUniformBrownianTime T n (i.val + 1)) -
        z (ginibreUniformBrownianTime T n i)‖ ^ 2 ≤ C) :
    Tendsto (fun n => ∑ i : Fin (n+1),
      itoTaylorRemainder f (z (ginibreUniformBrownianTime T n i))
        (z (ginibreUniformBrownianTime T n (i.val+1)) -
          z (ginibreUniformBrownianTime T n i))) atTop (𝓝 0) := by
  let K := z '' Set.Icc 0 T
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hz
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hzU t ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/(C+1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hd⟩ := itoTaylorRemainder_uniform_compact_open f U K hU hf hK hKU
    (ε/(C+1)) he
  filter_upwards [(itoUniformPathMesh_tendsto z T hz).eventually (gt_mem_nhds hδ)] with n hn
  rw [dist_zero_right]
  have hb (i : Fin (n+1)) : z (ginibreUniformBrownianTime T n i) ∈ K :=
    Set.mem_image_of_mem _ ⟨bot_le,
      ginibreUniformBrownianTime_le_end T n _ (Nat.le_of_lt i.is_lt)⟩
  calc
    _ ≤ ∑ i : Fin (n+1), ‖itoTaylorRemainder f (z (ginibreUniformBrownianTime T n i))
        (z (ginibreUniformBrownianTime T n (i.val+1))-
          z (ginibreUniformBrownianTime T n i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (n+1), (ε/(C+1))*
        ‖z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i)‖^2 :=
      Finset.sum_le_sum (fun i hi => hd _ (hb i) _
        ((itoUniformPathMesh_increment_le z T n i).trans_lt hn))
    _ = (ε/(C+1)) * ∑ i : Fin (n+1),
        ‖z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i)‖^2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (ε/(C+1))*C := mul_le_mul_of_nonneg_left (hq n) he.le
    _ < ε := by
      have h := mul_lt_mul_of_pos_left (show C < C+1 by linarith) he
      simpa only [div_mul_cancel₀ _ (show C+1 ≠ 0 by linarith)] using h

/-- The actual normalized Taylor error vanishes without any bound on quadratic sums. -/
theorem itoActualPathRemainder_div_quadratic_tendsto (f : E → ℝ) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (z : ℝ≥0 → E) (T : ℝ≥0)
    (hz : ContinuousOn z (Set.Icc 0 T)) (hzU : ∀ t ∈ Set.Icc 0 T, z t ∈ U) :
    Tendsto (fun n => itoActualPathTaylorRemainderSum f z T n /
      itoActualPathQuadraticSum z T n) atTop (𝓝 0) := by
  let K := z '' Set.Icc 0 T
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hz
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hzU t ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := itoTaylorRemainder_uniform_compact_open f U K hU hf hK hKU
    (ε/2) (half_pos hε)
  filter_upwards [(itoUniformPathMesh_tendsto z T hz).eventually (gt_mem_nhds hδ)] with n hn
  rw [dist_zero_right, norm_div]
  have hq : 0 ≤ itoActualPathQuadraticSum z T n := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  by_cases hzero : itoActualPathQuadraticSum z T n = 0
  · simp [hzero, hε]
  have hpos : 0 < itoActualPathQuadraticSum z T n := lt_of_le_of_ne hq (Ne.symm hzero)
  simp only [Real.norm_eq_abs, abs_of_nonneg hq]
  have hb (i : Fin (n+1)) : z (ginibreUniformBrownianTime T n i) ∈ K :=
    Set.mem_image_of_mem _ ⟨bot_le,
      ginibreUniformBrownianTime_le_end T n _ (Nat.le_of_lt i.is_lt)⟩
  have hr : ‖itoActualPathTaylorRemainderSum f z T n‖ ≤ (ε/2)*itoActualPathQuadraticSum z T n := by
    unfold itoActualPathTaylorRemainderSum itoActualPathQuadraticSum
    calc
      _ ≤ ∑ i : Fin (n+1), ‖itoTaylorRemainder f (z (ginibreUniformBrownianTime T n i))
          (z (ginibreUniformBrownianTime T n (i.val+1))-
            z (ginibreUniformBrownianTime T n i))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n+1), (ε/2)*
          ‖z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i)‖^2 :=
        Finset.sum_le_sum (fun i hi => hd _ (hb i) _
          ((itoUniformPathMesh_increment_le z T n i).trans_lt hn))
      _ = _ := (Finset.mul_sum _ _ _).symm
  exact ((div_le_iff₀ hpos).mpr hr).trans_lt (half_lt_self hε)

/-- Pathwise vanishing error normalized by one plus actual quadratic variation. -/
theorem itoActualPathRemainder_div_one_add_quadratic_tendsto (f : E → ℝ) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (z : ℝ≥0 → E) (T : ℝ≥0)
    (hz : ContinuousOn z (Set.Icc 0 T)) (hzU : ∀ t ∈ Set.Icc 0 T, z t ∈ U) :
    Tendsto (fun n => itoActualPathTaylorRemainderSum f z T n /
      (1+itoActualPathQuadraticSum z T n)) atTop (𝓝 0) := by
  let K := z '' Set.Icc 0 T
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hz
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hzU t ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := itoTaylorRemainder_uniform_compact_open f U K hU hf hK hKU
    (ε/2) (half_pos hε)
  filter_upwards [(itoUniformPathMesh_tendsto z T hz).eventually (gt_mem_nhds hδ)] with n hn
  rw [dist_zero_right, norm_div]
  have hq : 0 ≤ itoActualPathQuadraticSum z T n := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hpos : 0 < 1+itoActualPathQuadraticSum z T n := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos.le]
  have hb (i : Fin (n+1)) : z (ginibreUniformBrownianTime T n i) ∈ K :=
    Set.mem_image_of_mem _ ⟨bot_le,
      ginibreUniformBrownianTime_le_end T n _ (Nat.le_of_lt i.is_lt)⟩
  have hr : ‖itoActualPathTaylorRemainderSum f z T n‖ ≤ (ε/2)*itoActualPathQuadraticSum z T n := by
    unfold itoActualPathTaylorRemainderSum itoActualPathQuadraticSum
    calc
      _ ≤ ∑ i : Fin (n+1), ‖itoTaylorRemainder f (z (ginibreUniformBrownianTime T n i))
          (z (ginibreUniformBrownianTime T n (i.val+1))-
            z (ginibreUniformBrownianTime T n i))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n+1), (ε/2)*
          ‖z (ginibreUniformBrownianTime T n (i.val+1))-z (ginibreUniformBrownianTime T n i)‖^2 :=
        Finset.sum_le_sum (fun i hi => hd _ (hb i) _
          ((itoUniformPathMesh_increment_le z T n i).trans_lt hn))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hr' : ‖itoActualPathTaylorRemainderSum f z T n‖ ≤
      (ε/2)*(1+itoActualPathQuadraticSum z T n) :=
    hr.trans (mul_le_mul_of_nonneg_left (by linarith) (half_pos hε).le)
  exact ((div_le_iff₀ hpos).mpr hr').trans_lt (half_lt_self hε)

end
end GinibrePoincare
