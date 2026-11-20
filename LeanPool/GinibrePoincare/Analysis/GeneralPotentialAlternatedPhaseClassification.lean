/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialAlternatedPhaseClassification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialWeightedPolynomialPhase
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialPositivePhaseClosure

/-!
# General potential alternated phase classification

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialInverseAlternatedVector_positive_or_bottom_or_zero`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem potentialInverseAlternatedVector_positive_or_bottom_or_zero {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : PlanarPiLebesgueL2 n)
    (hF : F ∈ planarPiAlternatedWeightedMonomialVectors n n V) :
    (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F ∈
        potentialPositivePhaseVectors n hV.continuous hrot ∨
      (∃ P : ConfigurationPolynomial n, P.IsHomogeneous (vandermondeDegree n) ∧
        IsAlternatingConfigurationPolynomial P ∧
        (F : Configuration n → ℂ) =ᵐ[volume]
          fun z => MvPolynomial.eval z P * piPotentialHalfWeight n n V z) ∨ F = 0 := by
  obtain ⟨D, P, hp, ha, he⟩ := planarPiAlternatedWeightedMonomialVector_homogeneous_alternating n V
      F hF
  by_cases hz : P = 0
  · right; right
    apply weightedPolynomialL2_eq_zero F
    simpa only [hz] using he
  have hle := vandermondeDegree_le_of_homogeneous_alternating hp ha hz
  by_cases hbottom : D = vandermondeDegree n
  · right; left
    exact ⟨P, hbottom ▸ hp, ha, he⟩
  left
  refine ⟨D - vandermondeDegree n, by omega, ?_⟩
  intro a ha
  exact potentialInverseGauge_phase_degree hn hV.continuous hrot hfin hle F
    (fun a ha => volumeGlobalPhaseL2_weighted_homogeneous hrot P hp F he a ha) a ha

end
end GinibrePoincare
