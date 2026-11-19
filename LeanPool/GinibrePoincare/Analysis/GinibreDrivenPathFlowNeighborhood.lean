/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathFlowNeighborhood.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathContinuousLocalFlow

/-! Continuous noise selection stays locally in any prescribed configuration neighborhood. -/

@[expose] public section
open Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem drivenContinuousNoise_flow_stays_neighborhood
    (ε : ℝ) (hε : 0 < ε) (z : E)
    (Φ : drivenBoundedNoiseSpace E 1 → C(Icc 0 ε, E)) (hΦ : Continuous Φ)
    (hZero : ∀ N, Φ N ⟨0, ⟨le_rfl, hε.le⟩⟩ = z)
    (U : Set E) (hU : U ∈ nhds z) :
    ∃ δ > (0 : ℝ), ∃ τ > (0 : ℝ), τ ≤ ε ∧
      ∀ N (t : Icc 0 ε), ‖N.val‖ < δ → (t : ℝ) ≤ τ → Φ N t ∈ U := by
  let N₀ : drivenBoundedNoiseSpace E 1 := ⟨0, by simp⟩
  let t₀ : Icc 0 ε := ⟨0, ⟨le_rfl, hε.le⟩⟩
  have hEval : Continuous (fun p : drivenBoundedNoiseSpace E 1 × Icc 0 ε => Φ p.1 p.2) :=
    continuous_eval.comp ((hΦ.comp continuous_fst).prodMk continuous_snd)
  have hPre : (fun p : drivenBoundedNoiseSpace E 1 × Icc 0 ε => Φ p.1 p.2) ⁻¹' U ∈
      nhds (N₀, t₀) := hEval.continuousAt.preimage_mem_nhds (by simpa [t₀, hZero] using hU)
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hPre
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨δ, hδ, min ε (r/2), lt_min hε (by positivity), min_le_left _ _,?_⟩
  intro N t hN ht
  apply hVW (a := (N, t))
  constructor
  · apply hδV
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, N₀] using hN
  · apply hrW
    have htr : (t : ℝ) < r := lt_of_le_of_lt (ht.trans (min_le_right _ _)) (by linarith)
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, t₀, Real.norm_of_nonneg t.property.1]
        using htr

end
end GinibrePoincare
