/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathRiemannConvergence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathRiemann

/-! # Pathwise weighted increment convergence for vanishing-mesh partitions -/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem ginibreWeightedIncrements_tendsto_integral (w w' : ℝ → ℝ) (N : ℝ → E)
    (hw : ∀ s, HasDerivAt w (w' s) s) (hw' : Continuous w') (hN : Continuous N)
    (a b : ℝ) (hab : a ≤ b) (τ : ℕ → ℕ → ℝ) (count : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hτ : ∀ n, Monotone (τ n)) (hstart : ∀ n, τ n 0 = a)
    (hend : ∀ n, τ n (count n) = b)
    (hsize : ∀ n i, i < count n → τ n (i + 1) - τ n i ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (count n),
      w (τ n i) • (N (τ n (i + 1)) - N (τ n i))) atTop
      (𝓝 (w b • N b - w a • N a - ∫ s in a..b, w' s • N s)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw'.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (w' a)).trans (hC a ⟨le_rfl, hab⟩)
  have hUC : UniformContinuousOn N (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hN.continuousOn
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (C * (b - a) + 1)
  have hden : 0 < C * (b - a) + 1 := by nlinarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hmesh.eventually_lt_const hδ)
  refine ⟨M, ?_⟩
  intro n hn
  have hinterval (i : ℕ) (hi : i < count n) :
      a ≤ τ n i ∧ τ n (i + 1) ≤ b := by
    constructor
    · rw [← hstart n]; exact hτ n (Nat.zero_le i)
    · rw [← hend n]; exact hτ n (Nat.succ_le_of_lt hi)
  have hosc : ∀ i < count n, ∀ s ∈ uIoc (τ n i) (τ n (i + 1)),
      ‖N s - N (τ n (i + 1))‖ ≤ η := by
    intro i hi s hs
    rw [uIoc_of_le (hτ n (Nat.le_succ i))] at hs
    have hb := hinterval i hi
    have hsI : s ∈ Icc a b := ⟨hb.1.trans hs.1.le, hs.2.trans hb.2⟩
    have htI : τ n (i + 1) ∈ Icc a b :=
      ⟨hb.1.trans (hτ n (Nat.le_succ i)), hb.2⟩
    have hd : dist s (τ n (i + 1)) < δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
      have hh := hsize n i hi
      have hm := hM n hn
      linarith [hs.1]
    simpa only [dist_eq_norm] using (hclose s hsI _ htI hd).le
  have hbnd := ginibreWeightedIncrements_integral_error_bound w w' N hw hw' hN
    (τ n) (hτ n) (count n) C η hC0 hη.le
    (fun i hi s hs => by
      rw [uIoc_of_le (hτ n (Nat.le_succ i))] at hs
      have hb := hinterval i hi
      exact hC s ⟨hb.1.trans hs.1.le, hs.2.trans hb.2⟩) hosc
  rw [hstart n, hend n] at hbnd
  rw [dist_eq_norm]
  apply hbnd.trans_lt
  change C * (ε / (C * (b - a) + 1)) * (b - a) < ε
  calc
    _ = (C * ε * (b - a)) / (C * (b - a) + 1) := by ring
    _ < ε := (div_lt_iff₀ hden).2 (by nlinarith)

end
end GinibrePoincare
