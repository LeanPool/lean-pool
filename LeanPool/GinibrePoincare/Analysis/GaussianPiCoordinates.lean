/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianPiCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianLSIFiniteProduct
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Gaussian Pi Coordinates
-/


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Linear head/tail coordinates on a real finite tuple. -/
def gaussianFinConsEquiv (n : ℕ) :
    (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    (ContinuousLinearMap.pi (Fin.cases
      (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))
      (fun j => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))))
    ((ContinuousLinearMap.proj (0 : Fin (n + 1))).prod
      (ContinuousLinearMap.pi (fun j : Fin n => ContinuousLinearMap.proj j.succ)))
    (by intro p; ext <;> simp [Fin.cases])
    (by intro p; funext i; refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [ContinuousLinearMap.pi_apply, Fin.cases])

/-- Recursive product coordinates as an ordinary finite real tuple. -/
def gaussianProductCoordinates : (n : ℕ) →
    GaussianProductSpace n ≃L[ℝ] (Fin (n + 1) → ℝ)
  | 0 => ContinuousLinearEquiv.equivOfInverse
      (ContinuousLinearMap.pi (fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ))
      (ContinuousLinearMap.proj (0 : Fin 1))
      (by intro x; rfl)
      (by
        intro p
        funext i
        have hi : i = 0 := by omega
        subst i
        rfl)
  | n + 1 =>
      ((gaussianProductCoordinates n).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans
        ((ContinuousLinearEquiv.prodComm ℝ (Fin (n + 1) → ℝ) ℝ).trans
          (gaussianFinConsEquiv (n + 1)))

/-- Head/tail coordinates preserve the actual product Gaussian law. -/
theorem gaussianFinCons_measurePreserving (v : ℝ≥0) (n : ℕ) :
    MeasurePreserving (gaussianFinConsEquiv n)
      ((gaussianReal 0 v).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 v)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)) := by
  have hi : MeasurePreserving (gaussianFinConsEquiv n).symm
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v))
      ((gaussianReal 0 v).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 v))) := by
    convert! measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => gaussianReal 0 v) 0 using 1
  exact MeasurePreserving.symm (gaussianFinConsEquiv n).symm.toHomeomorph.toMeasurableEquiv hi

/-- The recursive Gaussian law is exactly the ordinary finite real Gaussian product. -/
theorem gaussianProductCoordinates_measurePreserving (v : ℝ≥0) (n : ℕ) :
    MeasurePreserving (gaussianProductCoordinates n) (gaussianProductLaw v n)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)) := by
  induction n with
  | zero =>
    have hi : MeasurePreserving (gaussianProductCoordinates 0).symm
        (Measure.pi (fun _ : Fin 1 => gaussianReal 0 v)) (gaussianReal 0 v) :=
      measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 v) 0
    exact MeasurePreserving.symm (gaussianProductCoordinates
      0).symm.toHomeomorph.toMeasurableEquiv hi
  | succ n ih =>
    have hp := ih.prod (MeasurePreserving.id (gaussianReal 0 v))
    have hs := Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin (n + 1) =>
      gaussianReal 0 v))
      (ν := gaussianReal 0 v)
    have h := (gaussianFinCons_measurePreserving v (n + 1)).comp (hs.comp hp)
    convert! h using 1

/-- Recursive coordinate directions become the ordinary coordinate basis vectors. -/
theorem gaussianProductCoordinates_direction (n : ℕ) (i : Fin (n + 1)) :
    gaussianProductCoordinates n (gaussianProductDirection n i) = Pi.single i 1 := by
  classical
  induction n with
  | zero =>
    funext j
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [gaussianProductCoordinates, gaussianProductDirection, gaussianFinConsEquiv]
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [gaussianProductCoordinates, gaussianProductDirection, gaussianFinConsEquiv, ih,
          Pi.single_apply]

/-- Actual coordinate gradient energy in the usual real finite product. -/
def gaussianPiEnergy (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2

theorem gaussianProductEnergy_coordinates (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ)
    (x : GaussianProductSpace n) :
    gaussianProductEnergy n (f ∘ gaussianProductCoordinates n) x =
      gaussianPiEnergy (n + 1) f (gaussianProductCoordinates n x) := by
  unfold gaussianProductEnergy gaussianPiEnergy
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    gaussianProductCoordinates_direction]

/-- The sharp compact Lipschitz Gaussian LSI in ordinary finite real coordinates. -/
theorem gaussianPi_lsi_compactLipschitz (v : ℝ≥0) (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    squareEntropy (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)) f ≤
      (2 * (v : ℝ)) * ∫ x, gaussianPiEnergy (n + 1) f x
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v) := by
  let T := gaussianProductCoordinates n
  have hp := gaussianProductCoordinates_measurePreserving v n
  have he := gaussianProduct_lsi_compactLipschitz v n (f ∘ T)
    (hf.comp T.lipschitzWith) (hc.comp_homeomorph T.toHomeomorph)
  have hent : squareEntropy (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)) f =
      squareEntropy (gaussianProductLaw v n) (f ∘ T) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ T.continuous.measurable.aemeasurable f
      (hf.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hf.continuous).aestronglyMeasurable
  have hm : Measurable (gaussianPiEnergy (n + 1) f) := by
    unfold gaussianPiEnergy
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_fderiv_apply_const ℝ f _).pow_const 2
  have henergy : (∫ x, gaussianPiEnergy (n + 1) f x
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 v)) =
      ∫ x, gaussianProductEnergy n (f ∘ T) x ∂gaussianProductLaw v n := by
    rw [← hp.map_eq, integral_map T.continuous.measurable.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (gaussianProductEnergy_coordinates n f x).symm))
  rw [hent, henergy]
  exact he

end
end GinibrePoincare
