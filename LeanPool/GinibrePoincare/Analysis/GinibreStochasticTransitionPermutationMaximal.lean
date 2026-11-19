/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticTransitionPermutationMaximal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationDynamics

/-!
# Ginibre stochastic transition permutation maximal

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreDrivenMaximalValue_permute`.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenMaximalLifetime_le_permute {n : ℕ} (σ : ParticlePermutation n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) :
    ginibreDrivenMaximalLifetime n α N z ≤
      ginibreDrivenMaximalLifetime n α (fun s => permute σ (N s)) (permute σ z) := by
  apply iSup_le
  intro T
  obtain ⟨X, hX⟩ := T.property
  exact ginibreDrivenHorizons_le_lifetime ⟨fun s => permute σ (X s), ginibreDrivenSegment_permute hX
      σ⟩

theorem ginibreDrivenMaximalLifetime_permute {n : ℕ} (σ : ParticlePermutation n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) :
    ginibreDrivenMaximalLifetime n α (fun s => permute σ (N s)) (permute σ z)=
      ginibreDrivenMaximalLifetime n α N z := by
  apply le_antisymm
  · have hi := ginibreDrivenMaximalLifetime_le_permute σ.symm α
      (fun s => permute σ (N s)) (permute σ z)
    have hz : permute σ.symm (permute σ z)=z := by
      funext i
      exact congrArg z (σ.apply_symm_apply i)
    have hN : (fun s => permute σ.symm (permute σ (N s)))=N := by
      funext s i
      exact congrArg (N s) (σ.apply_symm_apply i)
    rw [hz, hN] at hi
    exact hi
  · exact ginibreDrivenMaximalLifetime_le_permute σ α N z

theorem ginibreDrivenMaximalValue_permute {n : ℕ} (σ : ParticlePermutation n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) (t : ℝ≥0) :
    ginibreDrivenMaximalValue n α (fun s => permute σ (N s)) (permute σ z) t=
      permute σ (ginibreDrivenMaximalValue n α N z t) := by
  have hl := ginibreDrivenMaximalLifetime_permute σ α N z
  by_cases ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z
  · obtain ⟨T, X, hT, hX⟩ := ginibreDrivenMaximalLifetime_exists_segment t ht
    have hXp := ginibreDrivenSegment_permute hX σ
    have hp : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α
        (fun s => permute σ (N s)) (permute σ z) := by rw [hl]; exact ht
    rw [ginibreDrivenMaximalValue_eq_segment hXp t hT.le hp,
      ginibreDrivenMaximalValue_eq_segment hX t hT.le ht]
  · simp only [ginibreDrivenMaximalValue, hl, dite_eq_right ht]

end
end GinibrePoincare
