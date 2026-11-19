/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterDirection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterGlobalNonvanishing
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialDirection

/-! The normalized center direction of the actual original Brownian solution.
Continuity follows from proved center non-hitting, for positive initial center. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The map sending `z` to the configuration all of whose coordinates equal `∑ j, z j`. -/
def ginibreRepeatedCenterCLM (n : ℕ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun _ => coordinateSumCLM n

/-- The unit vector, in real coordinates, in the direction of `ginibreRepeatedCenterCLM n z`,
with fallback `e` when the coordinate sum vanishes. -/
def ginibreCenterRadialDirection (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  brownianRadialUnitVector (configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)) e

theorem ginibreCenterRadialDirection_norm (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖ = 1) (z : Configuration n) :
    ‖ginibreCenterRadialDirection n e z‖=1 := brownianRadialUnitVector_norm _ e he

theorem ginibreCenterRadialDirection_measurable (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Measurable (ginibreCenterRadialDirection n e) :=
  (brownianRadialUnitVector_measurable e).comp
    ((configurationEuclideanEquiv n).continuous.measurable.comp (ginibreRepeatedCenterCLM
        n).measurable)

theorem ginibreCenterRadialDirection_continuousAt {n : ℕ} (hn : 0 < n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n)
    (hz : ginibreCenterSquared n z ≠ 0) : ContinuousAt (ginibreCenterRadialDirection n e) z := by
  have hne : configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) ≠ 0 := by
    intro h
    have he : ginibreRepeatedCenterCLM n z = 0 :=
      (configurationEuclideanEquiv n).injective (by simpa using h)
    have hi := congrFun he (⟨0, hn⟩ : Fin n)
    have hs : coordinateSum z=0 := by
      simpa only [ginibreRepeatedCenterCLM, ContinuousLinearMap.pi_apply,
        coordinateSumCLM_apply, Pi.zero_apply] using hi
    apply hz
    simp [ginibreCenterSquared, hs]
  have hc : ContinuousAt (fun x => configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n x)) z
      :=
    ((configurationEuclideanEquiv n).continuous.comp (ginibreRepeatedCenterCLM
        n).continuous).continuousAt
  exact (brownianRadialUnitVector_continuousAt _ e hne).comp
    (f := fun x => configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n x)) hc

theorem ginibreBrownianMaximalProcess_centerDirection_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖ = 1) :
    let u := fun t ω => ginibreCenterRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B t ω)
    (∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin n × Fin 2))
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t)) ∧
    (∀ t ω, ‖u t ω‖=1) ∧ (∀ᵐ ω ∂P, Continuous (fun t => u t ω)) := by
  dsimp only
  obtain ⟨hAdapt, hPath⟩ := ginibreBrownianMaximalProcess_global_original_solution
    (by omega) α z hz B P hB hind
  refine ⟨fun t => (ginibreCenterRadialDirection_measurable n e).comp
    (hAdapt t).measurable, fun t ω => ginibreCenterRadialDirection_norm n e he _,?_⟩
  filter_upwards [hPath, ginibreBrownian_center_global_nonvanishing hn α z hz hcenter B P hB hind]
    with ω hω hnonzero
  have hX : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using hω.1.comp NNReal.continuous_coe
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (ginibreCenterRadialDirection_continuousAt (by omega) e _ (hnonzero t)).comp
    (f := fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B s ω) hX.continuousAt

end
end GinibrePoincare
