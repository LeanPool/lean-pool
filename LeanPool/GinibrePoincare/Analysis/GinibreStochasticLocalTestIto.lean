/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLocalTestIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactItoMartingale
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral

/-! # Localized Itô martingale for a C² test

Hamiltonian localization places the stopped process in a compact subset of
the collision-free open set. This allows a test with C² regularity on that
open set, even when it has no smooth extension across collisions.

The martingale and the two stopped identities follow from the localized
Itô integral construction. Use `GinibreStochasticLocalTestItoIntegral` when
the argument also needs convergence of the Brownian gradient sums. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_local_test_ito_martingale_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : ContDiffOn ℝ 2 f {x | CollisionFree x}) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        f (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-
          f z = J t ω+
            ∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α f
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) ∧
      ((fun ω => f (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω)) =ᵐ[P]
        (fun ω => f z+J (ginibreBrownianHamiltonianBoundedStop n α z B R T ω) ω+
          ∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
            ginibreRealPaperSpeedGenerator n α f
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω))) := by
  obtain ⟨J, hJM, hJC, hJL, hJ0, _, hIto, hTerminal⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists hn α z hz B P hB hind R hR T f hf
  exact ⟨J, hJM, hJC, hJL, hJ0, hIto, hTerminal⟩

end
end GinibrePoincare
