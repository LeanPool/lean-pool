/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianContinuation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianSublevels
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathCompactRestart

/-! Actual Hamiltonian control implies continuation of the singular driven equation. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_extend_of_hamiltonian_bounded {n : ℕ} (hn : 0 < n) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0 + N t + ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (hfree : ∀ t ∈ Ico 0 T, CollisionFree (X t))
    (B : ℝ) (hbound : ∀ t ∈ Ico 0 T, ginibreHamiltonian n (X t) ≤ B) :
    ∃ δ > (0 : ℝ), ∃ U : ℝ → Configuration n, EqOn U X (Ico 0 T) ∧
      ContinuousOn U (Icc 0 (T+δ)) ∧
      ∀ t ∈ Icc 0 (T+δ), CollisionFree (U t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t ∧
        U t = U 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u) := by
  exact ginibreDrivenPath_compact_extend_beyond n α N X hN T hT hX hInt hEq
    (ginibreHamiltonianSublevel n B) (ginibreHamiltonianSublevel_isCompact hn B)
    (fun z hz => hz.1) (fun t ht => ⟨hfree t ht, hbound t ht⟩)

theorem ginibreDrivenPath_finite_nonextendible_hamiltonian_unbounded {n : ℕ}
    (hn : 0 < n) (α : ℝ) (N X : ℝ → Configuration n) (hN : Continuous N)
    (T : ℝ) (hT : 0 < T) (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0 + N t + ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (hfree : ∀ t ∈ Ico 0 T, CollisionFree (X t))
    (hmax : ¬ ∃ δ > (0 : ℝ), ∃ U : ℝ → Configuration n, EqOn U X (Ico 0 T) ∧
      ContinuousOn U (Icc 0 (T+δ)) ∧
      ∀ t ∈ Icc 0 (T+δ), CollisionFree (U t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t ∧
        U t = U 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u)) :
    ∀ B : ℝ, ∃ t ∈ Ico 0 T, B < ginibreHamiltonian n (X t) := by
  intro B
  by_contra h
  push Not at h
  exact hmax (ginibreDrivenPath_extend_of_hamiltonian_bounded hn α N X hN T hT hX hInt hEq hfree B
      h)

end
end GinibrePoincare
