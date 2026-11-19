/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralRefinementBound.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralUniformSums

/-! Actual common-grid oscillations control differences of Brownian sums. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The maximal difference of `F` between the grid times `itoUniformNNTime T (n + 1) (k / (m + 1))`
and `itoUniformNNTime T (m + 1) (k / (n + 1))` for `k < (n + 1) * (m + 1)`, comparing the uniform
partitions of `[0, T]` into `n + 1` and `m + 1` steps. -/
def brownianUniformRefinementMesh {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n m : ℕ) : Ω → ℝ :=
  brownianCoefficientSampleMesh (κ := Fin ((n+1)*(m+1))) F
    (fun k => itoUniformNNTime T (n+1) (k.val/(m+1)))
    (fun k => itoUniformNNTime T (m+1) (k.val/(n+1)))

theorem brownianUniformLeftSum_difference_secondMoment_le_mesh {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (n m : ℕ) :
    (∫ ω, (brownianUniformLeftSum (B j) F T (n+1) ω-brownianUniformLeftSum (B j) F T (m+1) ω)^2 ∂P)
        ≤
      (T : ℝ)*(∫ ω, (brownianUniformRefinementMesh F T n m ω)^2 ∂P) := by
  have := Fintype.ofFinite ι
  let G := fun k : Fin ((n+1)*(m+1)) => fun ω =>
    F (itoUniformNNTime T (n+1) (k.val/(m+1))) ω-F (itoUniformNNTime T (m+1) (k.val/(n+1))) ω
  have hG (k : Fin ((n+1)*(m+1))) : MemLp (G k) 2 P := (hFi _).sub (hFi _)
  have hmax : Integrable (fun ω => (brownianUniformRefinementMesh F T n m ω)^2) P := by
    have hm : Measurable (brownianUniformRefinementMesh F T n m) :=
      brownianCoefficientSampleMesh_measurable F _ _ (fun t => (hF t).mono
        ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl)
    apply Integrable.mono' (integrable_finsetSum Finset.univ (fun k _ => (hG k).integrable_sq))
      (hm.pow_const 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    have he : ∃ k : Fin ((n+1)*(m+1)), brownianUniformRefinementMesh F T n m ω = ‖G k ω‖ := by
      obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => ‖G k ω‖)
      exact ⟨k, he⟩
    obtain ⟨k, hk⟩ := he
    rw [hk, norm_pow, Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Finset.single_le_sum (fun i _ => sq_nonneg (G i ω)) (Finset.mem_univ k))
  have hle (k : Fin ((n+1)*(m+1))) : (∫ ω, (G k ω)^2 ∂P) ≤
      ∫ ω, (brownianUniformRefinementMesh F T n m ω)^2 ∂P := by
    apply integral_mono (hG k).integrable_sq hmax
    intro ω
    have hh : ‖G k ω‖ ≤ brownianUniformRefinementMesh F T n m ω :=
      Finset.le_sup' (f := fun k => ‖G k ω‖) (Finset.mem_univ k)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [brownianUniformLeftSum_difference_secondMoment B P hB hind j F hF hFi T (n+1) (m+1)
      (Nat.succ_pos _) (Nat.succ_pos _)]
  calc
    _ ≤ (T : ℝ)/((n+1)*(m+1) : ℕ)*∑ _k : Fin ((n+1)*(m+1)),
        ∫ ω, (brownianUniformRefinementMesh F T n m ω)^2 ∂P :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hp : (((n+1)*(m+1) : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp

end
end GinibrePoincare
