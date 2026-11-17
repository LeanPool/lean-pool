/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianFiniteIndexLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianPiCoordinates

/-!
# Gaussian Finite Index LSI
-/


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Sharp Gaussian LSI for any nonempty finite coordinate index. -/
theorem gaussianFiniteIndex_lsi_compactLipschitz
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] (v : ℝ≥0)
    (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    squareEntropy (Measure.pi (fun _ : I => gaussianReal 0 v)) f ≤
      (2 * (v : ℝ)) * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x
        ∂Measure.pi (fun _ : I => gaussianReal 0 v) := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  let e : Fin (n + 1) ≃ I := (Fintype.equivFinOfCardEq hn).symm
  let T := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : I => ℝ) e
  have hp : MeasurePreserving T
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v))
      (Measure.pi (fun _ : I => gaussianReal 0 v)) :=
    measurePreserving_piCongrLeft (fun _ : I => gaussianReal 0 v) e
  have hd (j : Fin (n + 1)) : T (Pi.single j 1) = Pi.single (e j) 1 := by
    funext i
    simp [T, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft,
      Equiv.piCongrLeft', Pi.single_apply, Equiv.symm_apply_eq]
  have he := gaussianPi_lsi_compactLipschitz v n (f ∘ T)
    (hf.comp T.lipschitzWith) (hc.comp_homeomorph T.toHomeomorph)
  have hent : squareEntropy (Measure.pi (fun _ : I => gaussianReal 0 v)) f =
      squareEntropy (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)) (f ∘ T) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ T.continuous.measurable.aemeasurable f
      (hf.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hf.continuous).aestronglyMeasurable
  have hm : Measurable (directionalEnergy (fun i : I => Pi.single i 1) f) := by
    unfold directionalEnergy
    exact Finset.measurable_sum _ (fun i hi => (measurable_fderiv_apply_const ℝ f _).pow_const 2)
  have henergy (x : Fin (n + 1) → ℝ) : gaussianPiEnergy (n + 1) (f ∘ T) x =
      directionalEnergy (fun i : I => Pi.single i 1) f (T x) := by
    unfold gaussianPiEnergy directionalEnergy
    rw [ContinuousLinearEquiv.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hd]
    exact e.sum_comp (fun i : I => (fderiv ℝ f (T x) (Pi.single i 1)) ^ 2)
  have hi : (∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x
        ∂Measure.pi (fun _ : I => gaussianReal 0 v)) =
      ∫ x, gaussianPiEnergy (n + 1) (f ∘ T) x
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v) := by
    rw [← hp.map_eq, integral_map T.continuous.measurable.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (henergy x).symm))
  rw [hent, hi]
  exact he

end
end GinibrePoincare
