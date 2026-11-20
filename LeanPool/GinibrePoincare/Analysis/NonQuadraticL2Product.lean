/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticL2Product.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticProjectionTensorization
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-! # Actual products of weighted L² vectors
This constructs the pure tensors in the genuine product-measure L² space.
It is the concrete starting point for coordinate Bergman projections. -/

@[expose] public section
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

private theorem l2Product_integral_norm_sq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (u : Lp ℂ 2 μ) : (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [SFinite μ] [SFinite ν] in
/-- Actual products of L² representatives are square integrable under the
actual product measure, even when the factors have infinite total mass. -/
theorem l2ProductFunction_memLp (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    MemLp (fun z : X × Y => u z.1 * v z.2) 2 (μ.prod ν) := by
  have hsm : AEStronglyMeasurable (fun z : X × Y => u z.1 * v z.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable u).comp_fst.mul (Lp.aestronglyMeasurable v).comp_snd
  apply (memLp_two_iff_integrable_sq_norm hsm).2
  have hu := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have hv := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)
  convert hu.mul_prod hv using 1
  funext z
  rw [norm_mul, mul_pow]

/-- A genuine pure tensor in the product-measure Hilbert space. -/
def l2ProductVector (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (l2ProductFunction_memLp u v).toLp _

omit [SFinite μ] [SFinite ν] in
theorem l2ProductVector_coeFn (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductVector u v =ᵐ[μ.prod ν] (fun z : X × Y => u z.1 * v z.2) :=
  (l2ProductFunction_memLp u v).coeFn_toLp

/-- Actual pure tensors have the exact product norm. -/
theorem l2ProductVector_norm_sq (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ‖l2ProductVector u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [← l2Product_integral_norm_sq (μ.prod ν)]
  calc
    _ = ∫ z : X × Y, ‖u z.1‖ ^ 2 * ‖v z.2‖ ^ 2 ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [l2ProductVector_coeFn u v] with z hz
      rw [hz, norm_mul, mul_pow]
    _ = (∫ x, ‖u x‖ ^ 2 ∂μ) * ∫ y, ‖v y‖ ^ 2 ∂ν := integral_prod_mul (μ := μ) (ν := ν) (fun x => ‖u
        x‖ ^ 2) (fun y => ‖v y‖ ^ 2)
    _ = _ := by rw [l2Product_integral_norm_sq μ, l2Product_integral_norm_sq ν]

/-- Product-measure L² inner products are the genuine Hilbert tensor inner
products, proved through Fubini on the actual representatives. -/
theorem l2ProductVector_inner (u u' : Lp ℂ 2 μ) (v v' : Lp ℂ 2 ν) :
    ⟪l2ProductVector u v, l2ProductVector u' v'⟫_ℂ = ⟪u, u'⟫_ℂ * ⟪v, v'⟫_ℂ := by
  rw [L2.inner_def]
  calc
    _ = ∫ z : X × Y, ⟪u z.1, u' z.1⟫_ℂ * ⟪v z.2, v' z.2⟫_ℂ ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [l2ProductVector_coeFn u v, l2ProductVector_coeFn u' v'] with z hz hz'
      rw [hz, hz']
      simp only [RCLike.inner_apply, map_mul]
      ring
    _ = (∫ x, ⟪u x, u' x⟫_ℂ ∂μ) * ∫ y, ⟪v y, v' y⟫_ℂ ∂ν :=
      integral_prod_mul (μ := μ) (ν := ν) (fun x => ⟪u x, u' x⟫_ℂ) (fun y => ⟪v y, v' y⟫_ℂ)
    _ = _ := by rw [L2.inner_def, L2.inner_def]

omit [SFinite μ] [SFinite ν] in
theorem l2ProductVector_add_left (u u' : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductVector (u + u') v = l2ProductVector u v + l2ProductVector u' v := by
  apply Lp.ext
  have hau := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add u u')
  filter_upwards [l2ProductVector_coeFn (u + u') v, l2ProductVector_coeFn u v,
    l2ProductVector_coeFn u' v, Lp.coeFn_add (l2ProductVector u v) (l2ProductVector u' v), hau]
    with z hz hz1 hz2 hzadd hzu
  change (u + u') z.1 = u z.1 + u' z.1 at hzu
  rw [hz, hzadd]
  simp only [Pi.add_apply]
  rw [hz1, hz2, hzu, add_mul]

omit [SFinite μ] [SFinite ν] in
theorem l2ProductVector_add_right (u : Lp ℂ 2 μ) (v v' : Lp ℂ 2 ν) :
    l2ProductVector u (v + v') = l2ProductVector u v + l2ProductVector u v' := by
  apply Lp.ext
  have hav := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_add v v')
  filter_upwards [l2ProductVector_coeFn u (v + v'), l2ProductVector_coeFn u v,
    l2ProductVector_coeFn u v', Lp.coeFn_add (l2ProductVector u v) (l2ProductVector u v'), hav]
    with z hz hz1 hz2 hzadd hzv
  change (v + v') z.2 = v z.2 + v' z.2 at hzv
  rw [hz, hzadd]
  simp only [Pi.add_apply]
  rw [hz1, hz2, hzv, mul_add]

omit [SFinite μ] [SFinite ν] in
theorem l2ProductVector_smul_left (c : ℂ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductVector (c • u) v = c • l2ProductVector u v := by
  apply Lp.ext
  have hau := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c u)
  filter_upwards [l2ProductVector_coeFn (c • u) v, l2ProductVector_coeFn u v,
    Lp.coeFn_smul c (l2ProductVector u v), hau] with z hz hz1 hzsmul hzu
  change (c • u) z.1 = c • u z.1 at hzu
  rw [hz, hzsmul]
  simp only [Pi.smul_apply]
  rw [hz1, hzu]
  simp only [smul_eq_mul]
  ring

omit [SFinite μ] [SFinite ν] in
theorem l2ProductVector_smul_right (c : ℂ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductVector u (c • v) = c • l2ProductVector u v := by
  apply Lp.ext
  have hav := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (Lp.coeFn_smul c v)
  filter_upwards [l2ProductVector_coeFn u (c • v), l2ProductVector_coeFn u v,
    Lp.coeFn_smul c (l2ProductVector u v), hav] with z hz hz1 hzsmul hzv
  change (c • v) z.2 = c • v z.2 at hzv
  rw [hz, hzsmul]
  simp only [Pi.smul_apply]
  rw [hz1, hzv]
  simp only [smul_eq_mul]
  ring

/-- The actual product-vector map is complex bilinear. -/
def l2ProductBilinear : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) where
  toFun u :=
    { toFun := l2ProductVector u
      map_add' := l2ProductVector_add_right u
      map_smul' := fun c v => l2ProductVector_smul_right c u v }
  map_add' u u' := by
    apply LinearMap.ext
    intro v
    exact l2ProductVector_add_left u u' v
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    exact l2ProductVector_smul_left c u v

/-- The algebraic Hilbert tensor maps to the actual product L² space. -/
def l2ProductTensorMap : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  TensorProduct.lift l2ProductBilinear

omit [SFinite μ] [SFinite ν] in
@[simp] theorem l2ProductTensorMap_tmul (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    l2ProductTensorMap (u ⊗ₜ[ℂ] v) = l2ProductVector u v := rfl

/-- The algebraic tensor embedding preserves the actual complex inner
product for every finite sum, not merely for pure tensors. -/
theorem l2ProductTensorMap_inner
    (x y : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    ⟪l2ProductTensorMap x, l2ProductTensorMap y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | tmul u v =>
    induction y using TensorProduct.inductionOn with
    | tmul u' v' =>
      simp only [l2ProductTensorMap_tmul, l2ProductVector_inner, TensorProduct.inner_tmul]
    | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']

/-- The actual product-L² realization is an isometric complex tensor
embedding; no change of measure or synthetic product Hilbert space occurs. -/
def l2ProductTensorIsometry : (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) where
  toLinearMap := l2ProductTensorMap
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact congrArg Complex.re (l2ProductTensorMap_inner x x)

/-- Extension of the actual tensor embedding to the Hilbert completion. -/
def l2ProductCompletedTensorMap :
    UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  l2ProductTensorIsometry.toContinuousLinearMap.fromCompletion

/-- The completion extension still has the exact norm, established by
continuity from the actual algebraic tensors. -/
theorem l2ProductCompletedTensorMap_norm
    (x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) :
    ‖l2ProductCompletedTensorMap x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq l2ProductCompletedTensorMap.continuous.norm continuous_norm
  | ih x =>
    change ‖l2ProductTensorIsometry.toContinuousLinearMap.fromCompletion
      (x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν))‖ = _
    rw [ContinuousLinearMap.fromCompletion_apply_coe, UniformSpace.Completion.norm_coe]
    exact l2ProductTensorIsometry.norm_map x

/-- The completed Hilbert tensor embeds isometrically into the genuine
product-measure L² Hilbert space. -/
def l2ProductCompletedTensorIsometry :
    UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) where
  toLinearMap := l2ProductCompletedTensorMap.toLinearMap
  norm_map' := l2ProductCompletedTensorMap_norm

/-- Actual pure product vectors have the multiplicative Hilbert norm. -/
theorem l2ProductVector_norm (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ‖l2ProductVector u v‖ = ‖u‖ * ‖v‖ := by
  have h := l2ProductVector_norm_sq u v
  apply (sq_eq_sq₀ (norm_nonneg (l2ProductVector u v))
    (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp
  simpa only [mul_pow] using h

/-- The actual product-vector map is a bounded continuous complex bilinear
map, not merely an algebraic tensor realization. -/
def l2ProductContinuousBilinear : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  l2ProductBilinear.mkContinuous₂ 1 (fun u v => by
    change ‖l2ProductVector u v‖ ≤ _
    rw [l2ProductVector_norm, one_mul])

theorem l2ProductVector_continuous :
    Continuous (fun p : Lp ℂ 2 μ × Lp ℂ 2 ν => l2ProductVector p.1 p.2) :=
  l2ProductContinuousBilinear.continuous₂

end
end GinibrePoincare
