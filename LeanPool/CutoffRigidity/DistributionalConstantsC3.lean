/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSobolevConstants

/-! # Constant distributions tested on actual compact C³ functions -/

public section

namespace CutoffRigidity

open Set MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution

variable {d : ℕ}

/-- A zero distributional coordinate derivative makes every compact smooth
mollification have zero ordinary derivative in that coordinate. -/
theorem coordinateDerivative_bumpMollification_eq_zero_of_weak_c3
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * f y ∂volume) = 0)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    coordinateDerivative i (bumpMollification φ f) x = 0 := by
  let k := φ.normed (volume : Measure (EuclideanSpace ℝ (Fin d)))
  have hk : ContDiff ℝ 3 k := φ.contDiff_normed
  have hkc : HasCompactSupport k := φ.hasCompactSupport_normed
  let ψ := fun y => k (x - y)
  have hψ : ContDiff ℝ 3 ψ := hk.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    convert! hkc.comp_homeomorph (Homeomorph.subLeft x) using 1
  have hDψ (y : EuclideanSpace ℝ (Fin d)) :
      coordinateDerivative i ψ y = -coordinateDerivative i k (x - y) := by
    have hl : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin d) => x - z)
        (-(1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) y := by
      convert! (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x using 1
    have hc := (hk.differentiable (by norm_num) (x - y)).hasFDerivAt.comp y hl
    unfold coordinateDerivative
    have hh := congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      hc.fderiv
    simp only [comp_apply, neg_apply, map_neg] at hh
    convert! hh using 1
  have hw := hweak ψ hψ hψc i
  have hi : (∫ y, coordinateDerivative i ψ y * f y ∂volume) =
      -(∫ y, f y * coordinateDerivative i k (x - y) ∂volume) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by dsimp only; rw [hDψ]; ring)
  rw [hi] at hw
  have hz : (∫ y, f y * coordinateDerivative i k (x - y) ∂volume) = 0 := by linarith
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    ext
    simp [lsmul_apply]
  have heq : bumpMollification φ f = f ⋆[lsmul ℝ ℝ, volume] k := by
    simpa only [bumpMollification, k, hflip] using
      (convolution_flip (f := f) (g := k) (L := lsmul ℝ ℝ) (μ := volume))
  have hd := hkc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf (hk.of_le (by norm_num)) x
  have hdk : Continuous (fderiv ℝ k) := (hk.fderiv_right (m := 1) (by norm_num)).continuous
  rw [heq, coordinateDerivative, hd.fderiv,
    convolution_precompR_apply (L := lsmul ℝ ℝ) hf (hkc.fderiv ℝ) hdk]
  exact hz

/-- A locally integrable distribution with zero coordinate derivatives has
constant actual smooth mollifications on connected Euclidean space. -/
theorem bumpMollification_eq_const_of_weak_zero_c3
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * f y ∂volume) = 0)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) :
    bumpMollification φ f x = bumpMollification φ f 0 := by
  apply is_const_of_fderiv_eq_zero ((bumpMollification_contDiff φ hf).differentiable (by simp))
    (fun x => ?_) x 0
  apply ContinuousLinearMap.ext
  intro z
  rw [← inner_gradient_left]
  have hG : gradient (bumpMollification φ f) x = 0 := by
    ext i
    rw [← fderiv_single_eq_gradient_coordinate]
    exact coordinateDerivative_bumpMollification_eq_zero_of_weak_c3 hf hweak φ x i
  rw [hG, inner_zero_left, zero_apply]

/-- Actual locally integrable zero-gradient distributions are a.e. constants.
Normalized compact bumps approximate the original function a.e. by the
Lebesgue differentiation theorem already proved in Mathlib. -/
theorem ae_eq_const_of_locallyIntegrable_weak_derivative_zero_c3
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : LocallyIntegrable f volume)
    (hweak : ∀ (ψ : EuclideanSpace ℝ (Fin d) → ℝ), ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      ∀ i : Fin d, (∫ y, coordinateDerivative i ψ y * f y ∂volume) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ => c := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    ⟨1 / ((n : ℝ) + 1), 2 / ((n : ℝ) + 1), by positivity, by
      have hn : 0 < (n : ℝ) + 1 := by positivity
      exact (div_lt_div_iff_of_pos_right hn).mpr (by norm_num)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [φ, div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp
      hn).const_mul 2
  have hratio : ∀ᶠ n : ℕ in atTop, (φ n).rOut ≤ 2 * (φ n).rIn := by
    filter_upwards with n
    dsimp only [φ]
    ring_nf
    exact le_rfl
  have hAE := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hratio hf
  have hC (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      bumpMollification (φ n) f x = bumpMollification (φ n) f 0 :=
    bumpMollification_eq_const_of_weak_zero_c3 hf hweak (φ n) x
  obtain ⟨x₀, hx₀⟩ := hAE.exists
  refine ⟨f x₀, ?_⟩
  filter_upwards [hAE] with x hx
  have hx' : Tendsto (fun n => bumpMollification (φ n) f 0) atTop (𝓝 (f x)) := by
    have hxB : Tendsto (fun n => bumpMollification (φ n) f x) atTop (𝓝 (f x)) := by
      convert! hx using 1
    exact hxB.congr' (Filter.Eventually.of_forall (fun n => hC n x))
  have hx₀' : Tendsto (fun n => bumpMollification (φ n) f 0) atTop (𝓝 (f x₀)) := by
    have hxB : Tendsto (fun n => bumpMollification (φ n) f x₀) atTop (𝓝 (f x₀)) := by
      convert! hx₀ using 1
    exact hxB.congr' (Filter.Eventually.of_forall (fun n => hC n x₀))
  exact tendsto_nhds_unique hx' hx₀'


end CutoffRigidity
