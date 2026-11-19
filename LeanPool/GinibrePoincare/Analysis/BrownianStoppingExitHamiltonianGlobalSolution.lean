/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/BrownianStoppingExitHamiltonianGlobalSolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianNonexplosion

/-! The actual canonical adapted process is a global original Brownian-driven singular
solution when the genuine stopped Hamiltonian martingales are supplied. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_global_original_solution_ae_of_stopped_martingales
    {Ω : Type*} [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hIto : ∀ T : ℝ≥0, ∀ R : ℝ, ginibreHamiltonian n z < R → ∃ N : ℝ≥0 → Ω → ℝ,
      Martingale N (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ᵐ ω ∂P, Continuous (fun t => N t ω)) ∧ (N 0 =ᵐ[P] 0) ∧
      (fun ω => ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω))
          =ᵐ[P]
        (fun ω => ginibreHamiltonian n z + N (ginibreBrownianHamiltonianBoundedStop n α z B R T ω) ω
            +
          ∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
            ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n)
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T (Real.toNNReal s) ω))) :
    ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ => ginibreBrownianMaximalProcess n α z B (Real.toNNReal t) ω) ∧
      ginibreBrownianMaximalProcess n α z B 0 ω = z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (ginibreBrownianMaximalProcess n α z B (Real.toNNReal t) ω)) ∧
      IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω)
        (fun t : ℝ => ginibreBrownianMaximalProcess n α z B (Real.toNNReal t) ω) := by
  have hg := ginibreBrownianMaximalLifetime_top_ae_of_stopped_martingales hn α hα z hz B P hB hIto
  filter_upwards [hg, ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hglobal hNoise
  have hc := ginibreDrivenMaximalPath_global_of_lifetime_top hglobal
  refine ⟨hc.1, ?_, hc.2.2.1, ?_⟩
  · simpa only [ginibreDrivenMaximalPath, Real.toNNReal_zero, ginibreBrownianMaximalProcess] using
      hc.2.1
  · let X := fun t : ℝ => ginibreBrownianMaximalProcess n α z B (Real.toNNReal t) ω
    have he : IsGinibreDrivenPath n α (ginibreBrownianFullContinuousNoise n B α ω).val X := hc.2.2.2
    have hN : (ginibreBrownianFullContinuousNoise n B α ω).val = ginibreConfigurationBrownianNoise n
        B α ω :=
      funext hNoise
    change IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω) X
    rwa [hN] at he

end
end GinibrePoincare
