/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDrivenPathLocalUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathLocalExistence

/-! # Local pathwise uniqueness of the actual continuous-noise correction -/

@[expose] public section
open Set Metric Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenPath_continuous_noise_correction_unique (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) (Y Z : ℝ → Configuration n)
    (hY0 : Y 0 = z) (hZ0 : Z 0 = z)
    (hY : ∀ᶠ t in nhds 0, HasDerivAt Y (ginibreLangevinDrift n α (Y t + N t)) t)
    (hZ : ∀ᶠ t in nhds 0, HasDerivAt Z (ginibreLangevinDrift n α (Z t + N t)) t) :
    Y =ᶠ[nhds 0] Z := by
  obtain ⟨K, s, hs, hb⟩ := ginibreLangevinDrift_local_lipschitz n α z hz
  have hYc : ContinuousAt (fun t => Y t+N t) 0 := hY.self_of_nhds.continuousAt.add hN.continuousAt
  have hZc : ContinuousAt (fun t => Z t+N t) 0 := hZ.self_of_nhds.continuousAt.add hN.continuousAt
  have hYs : ∀ᶠ t in nhds 0, Y t+N t ∈ s := hYc.eventually (by
    dsimp only
    rw [hY0, hN0, add_zero]
    change s ∈ nhds z
    exact hs)
  have hZs : ∀ᶠ t in nhds 0, Z t+N t ∈ s := hZc.eventually (by
    dsimp only
    rw [hZ0, hN0, add_zero]
    change s ∈ nhds z
    exact hs)
  apply ODE_solution_unique_of_eventually (K := K)
    (v := fun t y => ginibreLangevinDrift n α (y+N t))
    (s := fun t => {y | y+N t ∈ s})
  · apply Filter.Eventually.of_forall
    intro t
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_add_right] using hb.dist_le_mul (x+N t) hx (y+N t) hy
  · exact hY.and hYs
  · exact hZ.and hZs
  · rw [hY0, hZ0]

end
end GinibrePoincare
