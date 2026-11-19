/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticNoncollision.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticHamiltonianIto
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianGlobalSolution

/-! # Infinite lifetime and the global original equation

The construction of the maximal Brownian solution and the criterion turning
stopped Hamiltonian martingales into infinite lifetime are imported from
`BrownianStoppingExitHamiltonianGlobalSolution`. This module supplies those
martingales using `GinibreStochasticHamiltonianIto`, including their identities
at the bounded stopping times.

The first theorem concludes that the maximal lifetime is infinite almost
surely. The second retains the strongly adapted process together with a
single full-measure event on which the path is continuous, starts at `z`,
remains collision-free, and solves the original driven equation at every
nonnegative time. Independence of the Brownian coordinates is used in the
construction of the Hamiltonian Itô martingales. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalLifetime_top_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ginibreBrownianMaximalLifetime n α z B ω=⊤ := by
  apply ginibreBrownianMaximalLifetime_top_ae_of_stopped_martingales hn α α.coe_nonneg z hz B P hB
  intro T R hR
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLocal, hTerminal⟩ :=
    ginibreBrownianHamiltonian_continuous_ito_martingale_exists hn α z hz B P hB hind R hR.le T
  exact ⟨J, hJM, Filter.Eventually.of_forall hJC, hJ0, hTerminal⟩

theorem ginibreBrownianMaximalProcess_global_original_solution
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianMaximalProcess n α z B) ∧
    ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ => ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∧
      ginibreBrownianMaximalProcess n α z B 0 ω=z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (ginibreBrownianMaximalProcess n α z B t.toNNReal ω)) ∧
      IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω)
        (fun t : ℝ => ginibreBrownianMaximalProcess n α z B t.toNNReal ω) := by
  refine ⟨ginibreBrownianMaximalProcess_stronglyAdapted hn α z B P hB,?_⟩
  apply ginibreBrownianMaximalProcess_global_original_solution_ae_of_stopped_martingales
    hn α α.coe_nonneg z hz B P hB
  intro T R hR
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLocal, hTerminal⟩ :=
    ginibreBrownianHamiltonian_continuous_ito_martingale_exists hn α z hz B P hB hind R hR.le T
  exact ⟨J, hJM, Filter.Eventually.of_forall hJC, hJ0, hTerminal⟩
end
end GinibrePoincare
