/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexProductLSI.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexProductTransport
public import LeanPool.GinibrePoincare.Analysis.GaussianFiniteIndexBoundedLSI

/-!
# Strong convex product LSI

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `coordinateGaussianTransport_product_lsi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff BigOperators NNReal
namespace GinibrePoincare
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in
theorem coordinateDirectionalEnergy_integrable (μ : Measure (I → ℝ)) [IsFiniteMeasure μ]
    (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    Integrable (directionalEnergy (fun i : I => Pi.single i 1) f) μ := by
  have hm : Measurable (directionalEnergy (fun i : I => Pi.single i 1) f) := by
    unfold directionalEnergy
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ f _).pow_const 2
  apply memLp_one_iff_integrable.mp
  apply memLp_of_bounded (a := 0) (b := (Fintype.card I : ℝ) * (K : ℝ)^2) _ hm.aestronglyMeasurable
      1
  apply Eventually.of_forall
  intro x
  refine ⟨Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_⟩
  unfold directionalEnergy
  calc
    _ ≤ ∑ i : I, (K : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hb : |fderiv ℝ f x (Pi.single i 1)| ≤ (K : ℝ) := by
        rw [← Real.norm_eq_abs]
        calc
          _ ≤ ‖fderiv ℝ f x‖ * ‖Pi.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (K : ℝ) := by
            have hn : ‖(Pi.single i (1 : ℝ) : I → ℝ)‖ = 1 := by
              have hh := congrArg (fun a : ℝ≥0 => (a : ℝ)) (Pi.nnNorm_single (G := fun _ : I => ℝ)
                  (i := i) (1 : ℝ))
              simpa using hh
            rw [hn, mul_one]
            exact norm_fderiv_le_of_lipschitz ℝ hf
      nlinarith [hb, abs_nonneg (fderiv ℝ f x (Pi.single i 1)), sq_abs (fderiv ℝ f x (Pi.single i
          1))]
    _ = _ := by simp

/-- Genuine finite-product LSI from coordinate Gaussian transports. -/
theorem coordinateGaussianTransport_product_lsi (ν : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (T : I → ℝ → ℝ)
    (hT : ∀ i, ContDiff ℝ 1 (T i))
    (hmap : ∀ i, (gaussianReal 0 1).map (T i) = ν i)
    (L : ℝ≥0) (hb : ∀ i x, |deriv (T i) x| ≤ (L : ℝ))
    (f : (I → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hfLip : LipschitzWith K f) (C : ℝ) (hC : 0 ≤ C) (hfBound : ∀ x, |f x| ≤ C) :
    squareEntropy (Measure.pi ν) f ≤
      (2 * (L : ℝ)^2) * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x ∂Measure.pi ν := by
  let Φ := coordinateQuantileTransport T
  let H := f ∘ Φ
  have hΦc := coordinateQuantileTransport_contDiff T hT
  have hΦlip := coordinateQuantileTransport_lipschitz T hT L hb
  have hHc : ContDiff ℝ 1 H := hf.comp hΦc
  have hHlip : LipschitzWith (K * L) H := hfLip.comp hΦlip
  have hpres := coordinateQuantileTransport_measurePreserving T ν (fun i => (hT
      i).continuous.measurable) hmap
  have hlsi := gaussianFiniteIndex_lsi_bounded_C1 I 1 H hHc C ((K * L : ℝ≥0) : ℝ)
    hC (fun x => hfBound (Φ x)) (fun x => norm_fderiv_le_of_lipschitz ℝ hHlip)
  have hent : squareEntropy (Measure.pi ν) f =
      squareEntropy (Measure.pi (fun _ : I => gaussianReal 0 1)) H := by
    rw [← hpres.map_eq]
    exact squareEntropy_map _ _ hΦc.continuous.measurable.aemeasurable f
      (hf.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hf.continuous).aestronglyMeasurable
  have hEs := coordinateDirectionalEnergy_integrable (Measure.pi (fun _ : I => gaussianReal 0 1)) H
      hHlip
  have hEt := coordinateDirectionalEnergy_integrable (Measure.pi ν) f hfLip
  have hEp := hpres.integrable_comp_of_integrable hEt
  have hEm : Measurable (directionalEnergy (fun i : I => Pi.single i 1) f) := by
    unfold directionalEnergy
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ f _).pow_const 2
  have he : (∫ x, directionalEnergy (fun i : I => Pi.single i 1) H x
      ∂Measure.pi (fun _ : I => gaussianReal 0 1)) ≤
      (L : ℝ)^2 * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x ∂Measure.pi ν := by
    calc
      _ ≤ ∫ x, (L : ℝ)^2 * directionalEnergy (fun i : I => Pi.single i 1) f (Φ x)
          ∂Measure.pi (fun _ : I => gaussianReal 0 1) := by
        apply integral_mono_ae hEs (hEp.const_mul _)
        exact Eventually.of_forall (coordinateQuantileTransport_energy T hT (L : ℝ) hb f
          (hf.differentiable (by norm_num)))
      _ = _ := by
        rw [integral_const_mul, ← hpres.map_eq,
          integral_map hΦc.continuous.measurable.aemeasurable hEm.aestronglyMeasurable]
  rw [hent]
  simp only [NNReal.coe_one, mul_one] at hlsi
  calc
    _ ≤ 2 * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) H x
      ∂Measure.pi (fun _ : I => gaussianReal 0 1) := hlsi
    _ ≤ 2 * ((L : ℝ)^2 * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x ∂Measure.pi ν) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

end
end GinibrePoincare
