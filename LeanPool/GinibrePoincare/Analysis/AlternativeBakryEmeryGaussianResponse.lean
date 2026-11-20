/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGaussianResponse.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGaussianNoiseLSI
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsGenerator
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! # Gaussian-coordinate gradient transfer from an actual Lipschitz response

The pointwise gradient estimate does not assume differentiability of the
response map. It follows from its Lipschitz estimate and differentiability
of the observable at the actual endpoint. The final entropy transfer still
requires a response map; identifying it with the concrete Langevin endpoint
and taking the equilibrium limit remain separate analytic obligations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Exact local derivative transfer through a Lipschitz response, even at
points where the response itself need not have a derivative. -/
theorem bakryEmeryResponse_observable_fderiv_bound
    (Φ : F → E) {K : ℝ≥0} (hΦ : LipschitzWith K Φ)
    (f : E → ℝ) (x : F) (hf : DifferentiableAt ℝ f (Φ x)) :
    ‖fderiv ℝ (fun y => f (Φ y)) x‖ ≤ (K : ℝ) * ‖gradient f (Φ x)‖ := by
  have hb (δ : ℝ) (hδ : 0 < δ) :
      ‖fderiv ℝ (fun y => f (Φ y)) x‖ ≤
        (‖fderiv ℝ f (Φ x)‖ + δ) * (K : ℝ) := by
    have hev := (isLittleO_iff.mp hf.hasFDerivAt.isLittleO) hδ
    have hlocal : ∀ᶠ z in 𝓝 (Φ x),
        ‖f z - f (Φ x)‖ ≤ (‖fderiv ℝ f (Φ x)‖ + δ) * ‖z - Φ x‖ := by
      filter_upwards [hev] with z hz
      calc
        ‖f z - f (Φ x)‖ ≤ ‖fderiv ℝ f (Φ x) (z - Φ x)‖ +
          ‖f z - f (Φ x) - fderiv ℝ f (Φ x) (z - Φ x)‖ := by
            simpa only [norm_sub_rev] using
              norm_le_insert (fderiv ℝ f (Φ x) (z - Φ x)) (f z - f (Φ x))
        _ ≤ ‖fderiv ℝ f (Φ x)‖ * ‖z - Φ x‖ + δ * ‖z - Φ x‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) hz
        _ = (‖fderiv ℝ f (Φ x)‖ + δ) * ‖z - Φ x‖ := by ring
    apply norm_fderiv_le_of_lip' ℝ (by positivity)
    filter_upwards [hΦ.continuous.continuousAt.tendsto.eventually hlocal] with y hy
    exact hy.trans (by
      calc
        (‖fderiv ℝ f (Φ x)‖ + δ) * ‖Φ y - Φ x‖ ≤
          (‖fderiv ℝ f (Φ x)‖ + δ) * ((K : ℝ) * ‖y - x‖) :=
          mul_le_mul_of_nonneg_left (hΦ.norm_sub_le y x) (by positivity)
        _ = ((‖fderiv ℝ f (Φ x)‖ + δ) * (K : ℝ)) * ‖y - x‖ := by ring)
  have ht : Tendsto (fun δ : ℝ => (‖fderiv ℝ f (Φ x)‖ + δ) * (K : ℝ))
      (𝓝[>] 0) (𝓝 (‖fderiv ℝ f (Φ x)‖ * (K : ℝ))) := by
    have hc : Continuous (fun δ : ℝ => (‖fderiv ℝ f (Φ x)‖ + δ) * (K : ℝ)) := by fun_prop
    simpa only [add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have he := ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hb δ hδ)
  have hn : ‖gradient f (Φ x)‖ = ‖fderiv ℝ f (Φ x)‖ := by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [hn, mul_comm]
  exact he

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The finite coordinate energy is the Hilbert dual norm squared. The
conversion is exact and does not replace the Euclidean norm by a sup norm. -/
theorem bakryEmeryGaussianCoordinate_energy_eq_norm
    (g : EuclideanSpace ℝ I → ℝ) (x : I → ℝ) :
    directionalEnergy (fun i : I => Pi.single i 1)
      (fun y => g (WithLp.toLp 2 y)) x =
      ‖fderiv ℝ g (WithLp.toLp 2 x)‖ ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)
  let G : (I → ℝ) → ℝ := fun y => g (WithLp.toLp 2 y)
  have hd : fderiv ℝ g (WithLp.toLp 2 x) =
      (fderiv ℝ G x).comp e.toContinuousLinearMap := by
    simpa only [Function.comp_def, e, G, PiLp.coe_continuousLinearEquiv,
      WithLp.toLp_ofLp, WithLp.ofLp_toLp] using
      e.comp_right_fderiv (f := G) (x := WithLp.toLp 2 x)
  have he (i : I) : fderiv ℝ G x (Pi.single i 1) =
      fderiv ℝ g (WithLp.toLp 2 x) (EuclideanSpace.basisFun I ℝ i) := by
    rw [hd]
    rw [EuclideanSpace.basisFun_apply]
    rfl
  unfold directionalEnergy
  change (∑ i, (fderiv ℝ G x (Pi.single i 1)) ^ 2) = _
  simp_rw [he]
  have h := bakryEmeryGibbsCarré_self (EuclideanSpace.basisFun I ℝ) g
    (WithLp.toLp 2 x)
  have hn : ‖gradient g (WithLp.toLp 2 x)‖ = ‖fderiv ℝ g (WithLp.toLp 2 x)‖ := by
    simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [hn] at h
  simpa only [bakryEmeryGibbsCarré, bakryEmeryGibbsDirectional, ← sq] using h

/-- Sharp pointwise Gaussian-coordinate energy transfer, derived from the
response's actual Euclidean Lipschitz estimate. -/
theorem bakryEmeryGaussianResponse_energy_bound
    (Φ : EuclideanSpace ℝ I → E) {K : ℝ≥0} (hΦ : LipschitzWith K Φ)
    (f : E → ℝ) (x : I → ℝ) (hf : DifferentiableAt ℝ f (Φ (WithLp.toLp 2 x))) :
    directionalEnergy (fun i : I => Pi.single i 1)
      (fun y => f (Φ (WithLp.toLp 2 y))) x ≤
      (K : ℝ) ^ 2 * ‖gradient f (Φ (WithLp.toLp 2 x))‖ ^ 2 := by
  rw [bakryEmeryGaussianCoordinate_energy_eq_norm (fun y => f (Φ y)) x]
  have h := bakryEmeryResponse_observable_fderiv_bound Φ hΦ f (WithLp.toLp 2 x) hf
  nlinarith [norm_nonneg (fderiv ℝ (fun y => f (Φ y)) (WithLp.toLp 2 x)),
    mul_nonneg K.coe_nonneg (norm_nonneg (gradient f (Φ (WithLp.toLp 2 x))))]

omit [DecidableEq I] in
/-- Finite Gaussian entropy transfer with the exact response coefficient.
The pointwise gradient energy is derived above, including the Euclidean
coordinate conversion; no response Jacobian certificate is supplied. -/
theorem bakryEmeryGaussianResponse_square_lsi [Nonempty I]
    (v : ℝ≥0) (hv : v ≠ 0)
    (Φ : EuclideanSpace ℝ I → E) {K : ℝ≥0} (hΦ : LipschitzWith K Φ)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {L : ℝ≥0} (hfL : LipschitzWith L f)
    (C : ℝ) (hfC : ∀ y, |f y| ≤ C) :
    squareEntropy (Measure.pi (fun _ : I => gaussianReal 0 v))
      (fun x => f (Φ (WithLp.toLp 2 x))) ≤
      (2 * (v : ℝ) * (K : ℝ) ^ 2) *
        ∫ x, ‖gradient f (Φ (WithLp.toLp 2 x))‖ ^ 2
          ∂Measure.pi (fun _ : I => gaussianReal 0 v) := by
  classical
  let μ := Measure.pi (fun _ : I => gaussianReal 0 v)
  have hfl : LipschitzWith _ (fun x : I → ℝ => f (Φ (WithLp.toLp 2 x))) :=
    (hfL.comp hΦ).comp (PiLp.lipschitzWith_toLp 2 (fun _ : I => ℝ))
  have hbase := bakryEmeryGaussianNoise_lsi_boundedLipschitz I v hv
    (fun x => f (Φ (WithLp.toLp 2 x))) hfl C (fun x => hfC _)
  have hgrad : Continuous (gradient f) := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hmeas : Continuous (fun x : I → ℝ => ‖gradient f (Φ (WithLp.toLp 2 x))‖ ^ 2) :=
    ((hgrad.comp hΦ.continuous).comp (PiLp.continuous_toLp 2 (fun _ : I => ℝ))).norm.pow 2
  have hb (x : I → ℝ) : ‖gradient f (Φ (WithLp.toLp 2 x))‖ ≤ (L : ℝ) := by
    have hn : ‖gradient f (Φ (WithLp.toLp 2 x))‖ =
        ‖fderiv ℝ f (Φ (WithLp.toLp 2 x))‖ := by
      simp only [gradient, LinearIsometryEquiv.norm_map]
    rw [hn]
    exact norm_fderiv_le_of_lipschitz ℝ hfL
  have hi : Integrable (fun x : I → ℝ => ‖gradient f (Φ (WithLp.toLp 2 x))‖ ^ 2) μ := by
    apply (integrable_const ((L : ℝ) ^ 2)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hb x, norm_nonneg (gradient f (Φ (WithLp.toLp 2 x)))]
  have henergy := integral_mono_of_nonneg (μ := μ)
    (ae_of_all _ (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    (hi.const_mul ((K : ℝ) ^ 2))
    (ae_of_all _ (fun x => bakryEmeryGaussianResponse_energy_bound Φ hΦ f x
      (hf.differentiable (by norm_num) _)))
  have hmul := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 2 * (v : ℝ) by positivity)
  rw [integral_const_mul] at hmul
  calc
    _ ≤ (2 * (v : ℝ)) * ∫ x, directionalEnergy (fun i : I => Pi.single i 1)
        (fun y => f (Φ (WithLp.toLp 2 y))) x ∂μ := hbase
    _ ≤ (2 * (v : ℝ)) * ((K : ℝ) ^ 2 *
        ∫ x, ‖gradient f (Φ (WithLp.toLp 2 x))‖ ^ 2 ∂μ) := hmul
    _ = _ := by ring

end
end GinibrePoincare
