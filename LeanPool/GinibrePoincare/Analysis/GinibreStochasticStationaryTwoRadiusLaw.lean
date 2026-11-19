/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticStationaryTwoRadiusLaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTwoRadiusEquilibriumLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOriginalEquilibriumMarginals

/-! # Joint Gamma law at equilibrium

The original equilibrium path law has Ginibre terminal marginal. Push that
marginal forward by the measurable pair of observables
`(ginibreCenterSquared, pairwiseRadius)` and use the static two-radius
factorization. The resulting product has Gamma shapes `1` and
`recenteredGammaShape n`, both at rate `1`.

This theorem describes the joint law at each fixed time, including zero
speed and zero horizon. Independence of the Brownian drivers is established
separately in `GinibreStochasticFullTwoRadiusRealization`. -/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreStationaryTwoRadiusPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreStationaryTwoRadiusPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Both actual original equilibrium CIR observables have the exact independent
Gamma joint law at every time, including zero speed and zero horizon. -/
theorem ginibreOriginalEquilibrium_two_radius_gamma_product {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => (ginibreCenterSquared n (x ⟨T, T.property, le_rfl⟩),
        pairwiseRadius (x ⟨T, T.property, le_rfl⟩))) =
      (gammaMeasure 1 1).prod (gammaMeasure (recenteredGammaShape n : ℝ) 1) := by
  have hm : Measurable (fun z : Configuration n => (ginibreCenterSquared n z, pairwiseRadius z)) :=
      by
    unfold ginibreCenterSquared pairwiseRadius coordinateSum
    fun_prop
  have he : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ), Configuration n) => x ⟨T, T.property,
      le_rfl⟩) :=
    (continuous_eval_const _).measurable
  have hl := ginibreOriginalEquilibriumPathLaw_terminal (by omega : 0<n) α P B hB hiB T
  have h := congrArg (fun ν : Measure (Configuration n) =>
    ν.map (fun z => (ginibreCenterSquared n z, pairwiseRadius z))) hl
  rw [Measure.map_map hm he, ginibreTwoRadius_equilibrium_gamma_product n hn] at h
  exact h

end
end GinibrePoincare
