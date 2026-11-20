/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticProductDbar.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticProductBergman
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticComplexTestInverse

/-! # Actual product Hörmander estimate on the separated compact core -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section

/-- The algebraic tensor product of two copies of the complex planar test space. -/
abbrev PlanarProductCompactTensor := PlanarComplexCompactTest ⊗[ℂ] PlanarComplexCompactTest

/-- The weighted value map on tensors of tests, `f ⊗ g ↦ (f w) ⊗ (g w)` in `L²(ℂ × ℂ)`, where
`w = exp (-n V / 2)`. -/
def planarProductWeightedValue (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductLebesgueL2 :=
  l2ProductTensorMap.comp (TensorProduct.map (planarComplexWeightedValueL2 n V hV)
    (planarComplexWeightedValueL2 n V hV))

/-- The weighted left `∂̄` on tensors of tests, `f ⊗ g ↦ (∂̄f w) ⊗ (g w)` in `L²(ℂ × ℂ)`, where
`w = exp (-n V / 2)`. -/
def planarProductWeightedDbarLeft (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductLebesgueL2 :=
  l2ProductTensorMap.comp (TensorProduct.map (planarComplexWeightedDbarL2 n V hV)
    (planarComplexWeightedValueL2 n V hV))

/-- The weighted right `∂̄` on tensors of tests, `f ⊗ g ↦ (f w) ⊗ (∂̄g w)` in `L²(ℂ × ℂ)`, where
`w = exp (-n V / 2)`. -/
def planarProductWeightedDbarRight (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductLebesgueL2 :=
  l2ProductTensorMap.comp (TensorProduct.map (planarComplexWeightedValueL2 n V hV)
    (planarComplexWeightedDbarL2 n V hV))

/-- The actual bounded inverse transports to the first coordinate of every
finite separated compact test, including arbitrary sums. -/
theorem planarProductLeft_inverse_action
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (f : PlanarProductCompactTensor) :
    l2ProductLeftOperator T (planarProductWeightedDbarLeft n V hV.continuous f) =
      planarProductWeightedValue n V hV.continuous f -
        planarLeftBergmanProjection n V hV (planarProductWeightedValue n V hV.continuous f) := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [planarProductWeightedDbarLeft, planarProductWeightedValue, LinearMap.comp_apply,
      TensorProduct.map_tmul, l2ProductTensorMap_tmul, l2ProductLeftOperator_pure, hT,
      planarLeftBergmanProjection, l2ProductLeftOperator_pure]
    change l2ProductBilinear (_ - _) _ = _
    simp only [map_sub, LinearMap.sub_apply]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]; abel

/-- The same genuine inverse acts in the second coordinate. -/
theorem planarProductRight_inverse_action
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (f : PlanarProductCompactTensor) :
    l2ProductRightOperator T (planarProductWeightedDbarRight n V hV.continuous f) =
      planarProductWeightedValue n V hV.continuous f -
        planarRightBergmanProjection n V hV (planarProductWeightedValue n V hV.continuous f) := by
  induction f using TensorProduct.inductionOn with
  | tmul f g =>
    simp only [planarProductWeightedDbarRight, planarProductWeightedValue, LinearMap.comp_apply,
      TensorProduct.map_tmul, l2ProductTensorMap_tmul, l2ProductRightOperator_pure, hT,
      planarRightBergmanProjection, l2ProductRightOperator_pure]
    change l2ProductBilinear _ (_ - _) = _
    rw [map_sub]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]; abel
/-- Genuine two-coordinate Hörmander bound with the exact scalar constant,
for every finite sum in the separated compact C² core. -/
theorem rhoSubharmonicPotential_product_compact_tensor_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (f : PlanarProductCompactTensor) :
    let F := planarProductWeightedValue n V hV.continuous f
    ‖F - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV F)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        (‖planarProductWeightedDbarLeft n V hV.continuous f‖ ^ 2 +
          ‖planarProductWeightedDbarRight n V hV.continuous f‖ ^ 2) := by
  obtain ⟨T, hnorm, hT⟩ := rhoSubharmonicPotential_exists_bounded_dbar_inverse n hn V ρ hρpos hV hρ
  let C := 2 / ((n : ℝ) * ρ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := Real.sq_sqrt hC
  have bound (S : PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2)
      (hb : ‖S‖ ≤ Real.sqrt C) (G : PlanarProductLebesgueL2) : ‖S G‖ ^ 2 ≤ C * ‖G‖ ^ 2 := by
    have h := (S.le_opNorm G).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg G))
    have hh := (sq_le_sq₀ (norm_nonneg (S G))
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg G))).mpr h
    simpa only [mul_pow, hs] using hh
  have hl := bound (l2ProductLeftOperator T) ((l2ProductLeftOperator_norm_le T).trans hnorm)
    (planarProductWeightedDbarLeft n V hV.continuous f)
  have hr := bound (l2ProductRightOperator T) ((l2ProductRightOperator_norm_le T).trans hnorm)
    (planarProductWeightedDbarRight n V hV.continuous f)
  rw [planarProductLeft_inverse_action n V hV T hT f] at hl
  rw [planarProductRight_inverse_action n V hV T hT f] at hr
  exact (planarBergman_product_projection_error n V hV _).trans
    ((add_le_add hl hr).trans_eq (mul_add C _ _).symm)

end
end GinibrePoincare
