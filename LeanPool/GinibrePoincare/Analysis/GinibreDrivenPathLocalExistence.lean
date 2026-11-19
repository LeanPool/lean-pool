/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathLocalExistence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathContinuousNoisePicard
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Genuine local collision-free existence for continuous additive noise -/

@[expose] public section
open Set Metric MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_continuous_noise_local_exists (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) :
    ∃ τ > (0 : ℝ), ∃ X : ℝ → Configuration n,
      ContinuousOn X (Icc 0 τ) ∧ X 0 = z ∧
      ∀ t ∈ Icc 0 τ, CollisionFree (X t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t ∧
        X t = z+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u) := by
  obtain ⟨Y, hY0, ε, hε, hY⟩ := ginibreDrivenPath_continuous_noise_local_correction n α z hz N hN
      hN0
  let X := fun t => Y t+N t
  have hX0 : X 0 = z := by simp [X, hY0, hN0]
  have hXcont : ContinuousAt X 0 := (hY 0 (by constructor <;> linarith)).continuousAt.add
      hN.continuousAt
  have hop : IsOpen {w : Configuration n | CollisionFree w} := by
    have he : {w : Configuration n | CollisionFree w} =
        (vandermonde : Configuration n → ℂ) ⁻¹' ({0}ᶜ : Set ℂ) := by
      ext w
      simp [← vandermonde_ne_zero_iff]
    rw [he]
    exact isClosed_singleton.isOpen_compl.preimage continuous_vandermonde
  have hev : ∀ᶠ t in nhds 0, CollisionFree (X t) := hXcont.eventually (by
    rw [hX0]
    exact hop.mem_nhds hz)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hev
  let τ := min ε δ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hte (t : ℝ) (ht : t ∈ Icc 0 τ) : t ∈ Ioo (-ε) ε := by
    have hmin := min_le_left ε δ
    dsimp [τ] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hcf (t : ℝ) (ht : t ∈ Icc 0 τ) : CollisionFree (X t) := by
    apply hδs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    have hmin := min_le_right ε δ
    dsimp [τ] at ht
    linarith [ht.2]
  have hYon : ContinuousOn Y (Icc 0 τ) :=
    fun t ht => (hY t (hte t ht)).continuousAt.continuousWithinAt
  have hXon : ContinuousOn X (Icc 0 τ) := hYon.add hN.continuousOn
  have hb : ContinuousOn (ginibreLangevinDrift n α) {w : Configuration n | CollisionFree w} :=
    fun w hw => (ginibreLangevinDrift_contDiffAt n α w hw).continuousAt.continuousWithinAt
  have hD : ContinuousOn (fun t => ginibreLangevinDrift n α (X t)) (Icc 0 τ) :=
    hb.comp hXon hcf
  refine ⟨τ, hτ, X, hXon, hX0, ?_⟩
  intro t ht
  have hus : uIcc (0 : ℝ) t ⊆ Icc 0 τ := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t := (hD.mono
      hus).intervalIntegrable
  refine ⟨hcf t ht, hint, ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hY u (hte u (hus hu))) hint
  change Y t+N t = z+N t+_
  rw [hFTC, hY0]
  abel

end
end GinibrePoincare
