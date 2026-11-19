/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroLampertiIncrementLocalization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiNoiseCoefficient
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiRegularization
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroDirection

/-! Deterministic localization of the genuine regularized Itô coefficients on
positive-start compact intervals. No assertion about the drift at zero is used. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterRegularized_generator_interval
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (a t : ℝ≥0) (hat : a ≤ t)
    (hfree : ∀ u ∈ Icc a t, CollisionFree (X u))
    (hlow : ∀ u ∈ Icc a t, δ < ginibreCenterSquared n (X u)) :
    (∫ r in (a : ℝ)..t, ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) =
    ∫ r in (a : ℝ)..t, ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (X r.toNNReal)) := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (a : ℝ) ≤ t from hat)] at hr
  have hu : r.toNNReal ∈ Icc a t := by
    constructor
    · exact_mod_cast (show (a : ℝ) ≤ (r.toNNReal : ℝ) by rw [Real.coe_toNNReal _ (a.coe_nonneg.trans
                                                           hr.1)]; exact hr.1)
    · exact (Real.toNNReal_le_iff_le_coe).mpr hr.2
  exact ginibreCenterSquareRootRegularized_generator hn α hδ _ (hfree _ hu) (hlow _ hu)

theorem ginibreCenterRegularized_noise_coordinate_interval
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (a t u : ℝ≥0)
    (hlow : ∀ v ∈ Icc a t, δ < ginibreCenterSquared n (X v))
    (hu : u ∈ Icc a t) (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*
      fderiv ℝ (ginibreCenterSquareRootRegularized n δ) (X u)
        (ginibreCoordinateDirection i) =
      Real.sqrt (2*(α : ℝ)/(n : ℝ))*ginibreCenterRadialDirection n e (X u) i := by
  rw [(ginibreCenterSquareRootRegularized_eventuallyEq hδ _ (hlow u hu)).fderiv_eq]
  exact ginibre_squareRootCenter_noise_coordinate hn α α.coe_nonneg _
    (hδ.trans (hlow u hu)) e i

theorem ginibreCenterRegularizedIto_positive_start_increment
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (z : Configuration n)
    (J : ℝ≥0 → ℝ) (a t : ℝ≥0) (hat : a ≤ t)
    (hfree : ∀ u ∈ Icc a t, CollisionFree (X u))
    (hlow : ∀ u ∈ Icc a t, δ < ginibreCenterSquared n (X u))
    (hIa : IntervalIntegrable (fun r : ℝ => ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) volume 0 a)
    (hIt : IntervalIntegrable (fun r : ℝ => ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) volume a t)
    (ha : ginibreCenterSquareRootRegularized n δ (X a) -
      ginibreCenterSquareRootRegularized n δ z = J a +
        ∫ r in (0 : ℝ)..a, ginibreRealPaperSpeedGenerator n α
          (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal))
    (ht : ginibreCenterSquareRootRegularized n δ (X t) -
      ginibreCenterSquareRootRegularized n δ z = J t +
        ∫ r in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α
          (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) :
    ginibreSquareRootCenter n (X t)-ginibreSquareRootCenter n (X a) =
      J t-J a + ∫ r in (a : ℝ)..t, ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (X r.toNNReal)) := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals hIa hIt
  have hea := ginibreCenterSquareRootRegularized_eq hδ (X a) (hlow a ⟨le_rfl, hat⟩).le
  have het := ginibreCenterSquareRootRegularized_eq hδ (X t) (hlow t ⟨hat, le_rfl⟩).le
  have he := ginibreCenterRegularized_generator_interval hn α δ hδ X a t hat hfree hlow
  rw [hea] at ha
  rw [het] at ht
  rw [← he]
  linarith

end
end GinibrePoincare
