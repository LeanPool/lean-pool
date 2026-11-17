/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialSmoothSobolevApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreRadialWeakSobolevApproximation

/-! # Smooth radial functions of finite Sobolev energy

The concrete spatial cutoffs put every globally smooth symmetric radial
function of finite weighted H¹ energy in the original smooth-core completion.
Compact support and a separate entropy-integrability hypothesis are unnecessary.
This settles the reverse approximation problem for this smooth subclass only.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreEuclideanGradient_mul {n : ℕ} (f χ : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ) (z : Configuration n) :
    ginibreEuclideanGradient (χ * f) z =
      χ z • ginibreEuclideanGradient f z + f z • ginibreEuclideanGradient χ z := by
  apply PiLp.ext
  intro k
  simp only [ginibreEuclideanGradient_coordinate, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
    (hf.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]

theorem radial_smooth_spatial_cutoff_core (n m : ℕ) (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    IsRadialSobolevCore ((ginibreSpatialCutoff n m) * f) := by
  obtain ⟨F, hF⟩ := hr
  refine ⟨⟨(ginibreSpatialCutoff_smooth n m).mul hf,
    (ginibreSpatialCutoff_compact n m).mul_right, ?_⟩, ?_⟩
  · intro σ z
    simp only [Pi.mul_apply, ginibreSpatialCutoff_symmetric n m σ z, hs σ z]
  · refine ⟨fun r => sobolevCutoff m (∑ i, r i) * F r, ?_⟩
    intro z
    simp only [Pi.mul_apply, ginibreSpatialCutoff, configurationNormSq, hF]

/-- Reverse smooth-core approximation for actual globally smooth finite-energy radial functions. -/
theorem radial_smooth_finiteEnergy_mem_sobolevClosure (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (hv : MemLp f 2 (ginibreMeasure n))
    (hd : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n)) :
    (hv.toLp f, hd.toLp (ginibreEuclideanGradient f)) ∈ radialSobolevClosure n := by
  let u := hv.toLp f
  let g := hd.toLp (ginibreEuclideanGradient f)
  apply isClosed_closure.mem_of_tendsto (ginibreWeakSpatialTruncation_tendsto n hn u g)
  apply Eventually.of_forall
  intro m
  apply subset_closure
  refine ⟨(ginibreSpatialCutoff n m) * f,
    radial_smooth_spatial_cutoff_core n m f hf hs hr, ?_, ?_⟩
  · apply (ginibreWeakSpatialTruncation_value_ae n hn u g m).trans
    filter_upwards [hv.coeFn_toLp] with z hz
    simp only [u] at hz ⊢
    simp only [hz, Pi.mul_apply]
  · apply (ginibreWeakSpatialTruncation_gradient_ae n hn u g m).trans
    filter_upwards [hv.coeFn_toLp, hd.coeFn_toLp] with z hz hz'
    simp only [u, g, hz, hz', ginibreEuclideanGradient_mul f _ hf
      (ginibreSpatialCutoff_smooth n m)]

/-- Every such function has genuine smooth compact radial approximants in both L² components. -/
theorem radial_smooth_finiteEnergy_exists_core_sequence (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (hv : MemLp f 2 (ginibreMeasure n))
    (hd : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n)) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧
      Tendsto q atTop (𝓝 (hv.toLp f, hd.toLp (ginibreEuclideanGradient f))) :=
  mem_closure_iff_seq_limit.mp
    (radial_smooth_finiteEnergy_mem_sobolevClosure n hn f hf hs hr hv hd)

/-- Sharp radial LSI for every globally smooth symmetric radial function with finite
weighted value and gradient L² norms, without compact support or an entropy premise. -/
theorem radial_smooth_finiteEnergy_lsi (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (hv : MemLp f 2 (ginibreMeasure n))
    (hd : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n)) :
    Integrable (fun z => f z ^ 2 * Real.log (f z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n f ≤ smoothGinibreEnergy n f := by
  have h := radial_sobolev_lsi n hn
    (hv.toLp f, hd.toLp (ginibreEuclideanGradient f))
    (radial_smooth_finiteEnergy_mem_sobolevClosure n hn f hf hs hr hv hd)
  constructor
  · apply h.1.congr
    filter_upwards [hv.coeFn_toLp] with z hz
    simp only [hz]
  · have he : ‖hd.toLp (ginibreEuclideanGradient f)‖ ^ 2 =
        ∫ z, realGradientNormSq f z ∂ginibreMeasure n := by
      rw [← integral_norm_sq_eq_L2_norm_sq]
      apply integral_congr_ae
      filter_upwards [hd.coeFn_toLp] with z hz
      rw [hz, ginibreEuclideanGradient_norm_sq]
    have hb := h.2
    change squareEntropy (ginibreMeasure n) (hv.toLp f) ≤
      (1 / (n : ℝ)) * ‖hd.toLp (ginibreEuclideanGradient f)‖ ^ 2 at hb
    rw [squareEntropy_congr_ae _ hv.coeFn_toLp, he] at hb
    exact hb

end
end GinibrePoincare
