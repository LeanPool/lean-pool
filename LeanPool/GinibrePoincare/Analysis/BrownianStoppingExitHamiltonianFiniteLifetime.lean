/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianFiniteLifetime.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedPath

/-! Every finite-lifetime event reaches each high Hamiltonian level before the bounded stop. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalLifetime_le_hamiltonian_level {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) (hDeath : ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)) :
    ginibreBrownianHamiltonianFirstLevel n α z B R ω ≤ (T : ℝ≥0∞) :=
  (ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T).mpr (Or.inl hDeath)

theorem ginibreBrownianMaximalLifetime_le_stopped_hamiltonian_eq {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) (hDeath : ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)) :
    ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω) = R := by
  have hs := ginibreDrivenHamiltonianBoundedStop_le n α
    (ginibreBrownianFullContinuousNoise n B α ω).val z R T
  change ginibreHamiltonian n (ginibreDrivenMaximalValue n α
    (ginibreBrownianFullContinuousNoise n B α ω).val z
    (min T (ginibreDrivenHamiltonianBoundedStop n α
      (ginibreBrownianFullContinuousNoise n B α ω).val z R T))) = R
  rw [min_eq_right hs]
  exact ginibreDrivenHamiltonianBoundedStop_hamiltonian_eq hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T
    (ginibreBrownianMaximalLifetime_le_hamiltonian_level hn α z hz B R hR T ω hDeath)

end
end GinibrePoincare
