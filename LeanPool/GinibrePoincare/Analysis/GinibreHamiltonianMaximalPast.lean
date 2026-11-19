/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalPast.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalCausality

/-! Both existence up to a fixed time and maximal path values depend only on the past noise. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenHorizons_iff_lt_lifetime {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} (hN : Continuous N) (hN0 : N 0 = 0)
    (T : ℝ≥0) : T ∈ ginibreDrivenHorizons n α N z ↔
      (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
  constructor
  · rintro ⟨X, hX⟩
    exact hX.horizon_lt_lifetime hN hN0
  · intro hT
    exact ⟨ginibreDrivenMaximalPath n α N z, ginibreDrivenMaximalPath_segment T hT⟩

theorem GinibreDrivenSegment.change_noise {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z : Configuration n} {T : ℝ≥0} {X : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hnoise : EqOn N M (Icc 0 (T : ℝ))) :
    GinibreDrivenSegment n α M z T X := by
  refine ⟨hX.1, hX.2.1, ?_⟩
  intro t ht
  have hx := hX.2.2 t ht
  exact ⟨hx.1, hx.2.1, by rw [← hnoise ht]; exact hx.2.2⟩

theorem ginibreDrivenMaximalLifetime_past_invariant {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z : Configuration n}
    (hN : Continuous N) (hN0 : N 0 = 0) (hM : Continuous M) (hM0 : M 0 = 0)
    (T : ℝ≥0) (hnoise : EqOn N M (Icc 0 (T : ℝ))) :
    ((T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) ↔
      ((T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α M z) := by
  rw [← ginibreDrivenHorizons_iff_lt_lifetime hN hN0,
    ← ginibreDrivenHorizons_iff_lt_lifetime hM hM0]
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨X, hX.change_noise hnoise⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, hX.change_noise hnoise.symm⟩

theorem ginibreDrivenMaximalValue_past_invariant {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z : Configuration n}
    (hN : Continuous N) (hN0 : N 0 = 0) (hM : Continuous M) (hM0 : M 0 = 0)
    (T : ℝ≥0) (hnoise : EqOn N M (Icc 0 (T : ℝ))) :
    ginibreDrivenMaximalValue n α N z T = ginibreDrivenMaximalValue n α M z T := by
  have hiff := ginibreDrivenMaximalLifetime_past_invariant (α := α) (z := z) hN hN0 hM hM0 T hnoise
  by_cases hT : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z
  · have he := ginibreDrivenMaximalPath_noise_causal T hT (hiff.mp hT) hnoise
    have hr := he ⟨T.property, le_rfl⟩
    change ginibreDrivenMaximalValue n α N z (Real.toNNReal (T : ℝ)) =
      ginibreDrivenMaximalValue n α M z (Real.toNNReal (T : ℝ)) at hr
    rw [Real.toNNReal_coe] at hr
    exact hr
  · have hTM := fun h => hT (hiff.mpr h)
    simp only [ginibreDrivenMaximalValue, dite_eq_right hT, dite_eq_right hTM]

end
end GinibrePoincare
