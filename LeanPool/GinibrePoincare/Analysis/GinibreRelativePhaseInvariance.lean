/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreRelativePhaseInvariance.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EquilibriumProbability
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import LeanPool.GinibrePoincare.Analysis.PairwiseRadius

/-!
# Ginibre relative phase invariance

Part of the ginibre measure and holomorphic geometry development of the
Ginibre Poincaré formalization.

Main results: `recentered_ginibreRelativeQuarterTurn`,
`pairwiseRadius_ginibreRelativeQuarterTurn`, `measurePreserving_ginibreRelativeQuarterTurn`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Rotate the relative configuration by a quarter turn, fixing its center. -/
def ginibreRelativeQuarterTurn (n : ℕ) (z : Configuration n) : Configuration n :=
  fun i => coordinateSum z/(n : ℂ)+Complex.I*recenteredConfiguration n z i

theorem coordinateSum_ginibreRelativeQuarterTurn {n : ℕ} (hn : 0 < n) (z : Configuration n) :
    coordinateSum (ginibreRelativeQuarterTurn n z)=coordinateSum z := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  simp only [ginibreRelativeQuarterTurn, coordinateSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,← Finset.mul_sum]
  change (n : ℂ)*(coordinateSum z/(n : ℂ))+Complex.I*coordinateSum (recenteredConfiguration n
      z)=coordinateSum z
  rw [coordinateSum_recentered, mul_zero, add_zero]
  exact mul_div_cancel₀ _ hnC

theorem recentered_ginibreRelativeQuarterTurn {n : ℕ} (hn : 0 < n) (z : Configuration n) :
    recenteredConfiguration n (ginibreRelativeQuarterTurn n z)=fun i =>
        Complex.I*recenteredConfiguration n z i := by
  ext i
  simp only [recenteredConfiguration, projectToOrthogonal]
  rw [coordinateSum_ginibreRelativeQuarterTurn hn]
  simp only [ginibreRelativeQuarterTurn, recenteredConfiguration, projectToOrthogonal]
  ring

theorem pairwiseRadius_ginibreRelativeQuarterTurn (n : ℕ) (z : Configuration n) :
    pairwiseRadius (ginibreRelativeQuarterTurn n z)=pairwiseRadius z := by
  unfold pairwiseRadius
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have he : ginibreRelativeQuarterTurn n z j-ginibreRelativeQuarterTurn n z k=Complex.I*(z j-z k) :=
      by
    simp only [ginibreRelativeQuarterTurn, recenteredConfiguration, projectToOrthogonal]
    ring
  rw [he, Complex.normSq_mul]
  simp

/-- Rotation by a quarter turn, i.e. multiplication by `I`, on the zero-sum hyperplane. -/
def recenteredQuarterTurn (n : ℕ) (w : zeroSumHyperplane n) : zeroSumHyperplane n := Complex.I • w

theorem measurePreserving_recenteredQuarterTurn {n : ℕ} (hn : 0 < n) :
    MeasurePreserving (recenteredQuarterTurn n) (recenteredGinibreMeasure n)
        (recenteredGinibreMeasure n) := by
  have hm : Measurable (recenteredQuarterTurn n) := by
    unfold recenteredQuarterTurn
    exact ((continuous_const : Continuous (fun _ : zeroSumHyperplane n => Complex.I)).smul
        continuous_id).measurable
  have he : recenteredQuarterTurn n ∘ recenteredCoordinate n=recenteredCoordinate n ∘ globalPhase
      Complex.I := by
    funext z
    apply Subtype.ext
    ext i
    simp only [Function.comp_apply, recenteredQuarterTurn, recenteredCoordinate,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, globalPhase, recenteredConfiguration,
      projectToOrthogonal, coordinateSum,← Finset.mul_sum]
    ring
  refine ⟨hm,?_⟩
  change ((ginibreMeasure n).map (recenteredCoordinate n)).map (recenteredQuarterTurn n)=_
  rw [Measure.map_map hm (measurable_recenteredCoordinate n), he,
    ← Measure.map_map (measurable_recenteredCoordinate n)
        (measurePreserving_globalPhase_ginibreMeasure hn Complex.I (by simp)).measurable,
    (measurePreserving_globalPhase_ginibreMeasure hn Complex.I (by simp)).map_eq]
  rfl

/-- Genuine Ginibre invariance under relative quarter-turn, obtained from the
actual center/relative product law and global-phase invariance of its marginal. -/
theorem measurePreserving_ginibreRelativeQuarterTurn {n : ℕ} (hn : 0 < n) :
    MeasurePreserving (ginibreRelativeQuarterTurn n) (ginibreMeasure n) (ginibreMeasure n) := by
  let := recenteredGinibreMeasure_isProbabilityMeasure n hn
  let e := equilibriumMeasurableCoordinates n hn
  have hE : MeasurePreserving e (ginibreMeasure n)
      (standardComplexGaussianMeasure.prod (recenteredGinibreMeasure n)) :=
    ⟨e.measurable, equilibrium_jointLaw n hn⟩
  have hP := (MeasurePreserving.id standardComplexGaussianMeasure).prod
    (measurePreserving_recenteredQuarterTurn hn)
  have hInv := MeasurePreserving.symm e hE
  convert hInv.comp (hP.comp hE) using 1
  funext z
  rfl

end
end GinibrePoincare
