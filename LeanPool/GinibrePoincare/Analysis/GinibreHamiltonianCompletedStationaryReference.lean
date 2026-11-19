/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCompletedStationaryReference.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCompletedProductBrownian
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianActualStationaryOUReversal

/-!
# Ginibre Hamiltonian completed stationary reference

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreHamiltonian_completed_product_killed_action_reverse`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths over the horizon `[0, T]`. -/
local instance ginibreCompletedStationaryReferencePathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreCompletedStationaryReference_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Actual stationary killed OU action reversal on the explicit completed
Gaussian-coordinate/original-Brownian product. All initial independence and
Brownian transport properties are derived internally. -/
theorem ginibreHamiltonian_completed_product_killed_action_reverse {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (R : ℝ) :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    let ν := γ.prod P
    let Q := ν.completion
    let A := fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
      ginibreHamiltonianOUJointHorizonPath n α T
        (ginibreHamiltonianOUCoordinateAssembly n x.1,
          ginibreBrownianFullContinuousNoise n (fun i t y => B i t y.2) α x)
    ((Q.map A).withDensity (fun x => ENNReal.ofReal
      (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      (Q.map A).withDensity (fun x => ENNReal.ofReal
        (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x)) := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let ν := γ.prod P
  let Q := ν.completion
  let Ωc := NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν
  have : IsProbabilityMeasure Q := ginibre_completion_isProbabilityMeasure ν
  let Bc : (Fin n × Fin 2) → ℝ≥0 → Ωc → ℝ := fun i t x => B i t x.2
  let Z : (Fin n × Fin 2) → Ωc → ℝ := fun i x => x.1 i
  have hBc : ∀ i, IsBrownianReal (Bc i) Q := ginibreBrownian_completed_initial_noise_product γ P B
      hB
  have hZ (i : Fin n × Fin 2) : HasLaw (Z i) (gaussianReal 0 (1/2)) Q :=
    (measurePreserving_eval (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2)) i).hasLaw.comp
      (ginibreCompletedProduct_fst_preserving γ P).hasLaw
  have hiZ : iIndepFun Z Q := ginibre_iIndepFun_precompose_measurePreserving Q γ _
    (ginibreCompletedProduct_fst_preserving γ P) (fun i x => x i)
      (fun i => measurable_pi_apply i)
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id))
  have hiBc : iIndepFun (fun i x t => Bc i t x) Q :=
    ginibreBrownian_completed_product_independent_coordinates γ P B hB hiB
  have hm : Measurable (fun ω i t => B i t ω) :=
    Measurable.of_eval (fun i => Measurable.of_eval
      (fun t => aemeasurable_iff_measurable.mp ((hB i).aemeasurable t)))
  have hind : IndepFun (fun x i => Z i x) (fun x i t => Bc i t x) Q :=
    (ginibreCompletedProduct_initial_noise_independent γ P).comp measurable_id hm
  exact ginibreHamiltonian_actual_stationary_killed_action_reverse hn α hα Q Bc hBc Z hZ hiZ hiBc
      hind T R

end
end GinibrePoincare
