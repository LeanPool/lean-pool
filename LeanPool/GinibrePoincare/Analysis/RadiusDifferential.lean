/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadiusDifferential.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PairwiseRadius
public import LeanPool.GinibrePoincare.Analysis.ComplexGeneratorCalculus

/-!
# Radius differential

Part of the polynomial, radial and equilibrium sectors development of the
Ginibre Poincaré formalization.

Main results: `complexRadius_confinement`, `complexRadius_coulomb`, `complexRadius_realDirection`,
`complexRadius_imaginaryDirection`.
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Complexification of the paper's real pair-distance radius. -/
def complexRadius (n : ℕ) (z : Configuration n) : ℂ := (pairwiseRadius z : ℂ)

/-- Polarization of the pair-distance quadratic form. -/
def radiusBilinear (n : ℕ) (z v : Configuration n) : ℂ :=
  (n : ℂ) * ∑ j, z j * conj (v j) - coordinateSum z * conj (coordinateSum v)

theorem complexRadius_eq (n : ℕ) (z : Configuration n) :
    complexRadius n z = radiusBilinear n z z := by
  simp only [complexRadius, pairwiseRadius_eq_normSq, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_natCast, configurationNormSq, Complex.ofReal_sum,
    ← Complex.mul_conj, radiusBilinear]

/-- Linear part of the polarized radius in its first argument. -/
def radiusLeftCLM (n : ℕ) (v : Configuration n) : Configuration n →L[ℝ] ℂ :=
  (n : ℂ) • (∑ j, conj (v j) • ContinuousLinearMap.proj j) -
    conj (coordinateSum v) • coordinateSumCLM n

@[simp] theorem radiusLeftCLM_apply (n : ℕ) (v z : Configuration n) :
    radiusLeftCLM n v z = radiusBilinear n z v := by
  simp [radiusLeftCLM, radiusBilinear, mul_comm]

/-- Linear part of the polarized radius in its second argument, over `ℝ`. -/
def radiusRightCLM (n : ℕ) (v : Configuration n) : Configuration n →L[ℝ] ℂ :=
  (n : ℂ) • (∑ j, v j • (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj j))) -
    coordinateSum v • (Complex.conjCLE.toContinuousLinearMap.comp (coordinateSumCLM n))

@[simp] theorem radiusRightCLM_apply (n : ℕ) (v z : Configuration n) :
    radiusRightCLM n v z = radiusBilinear n v z := by
  simp [radiusRightCLM, radiusBilinear]

/-- The complexified radius is a smooth quadratic observable. -/
theorem differentiable_complexRadius (n : ℕ) : Differentiable ℝ (complexRadius n) := by
  have heq : complexRadius n = fun z =>
      (n : ℂ) * ∑ j, z j * conj (z j) - coordinateSumCLM n z * conj (coordinateSumCLM n z) := by
    funext z; simp [complexRadius_eq, radiusBilinear]
  rw [heq]
  fun_prop

private theorem fderiv_conj_coordinate (n : ℕ) (j : Fin n) (z v : Configuration n) :
    fderiv ℝ (fun w : Configuration n => conj (w j)) z v = conj (v j) := by
  change fderiv ℝ (Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj j)) z v = _
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem fderiv_conj_sum (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (fun w : Configuration n => conj (coordinateSum w)) z v = conj (coordinateSum v) := by
  have heq : (fun w : Configuration n => conj (coordinateSum w)) =
      Complex.conjCLE.toContinuousLinearMap.comp (coordinateSumCLM n) := by
    funext w; simp
  rw [heq, ContinuousLinearMap.fderiv]
  simp

/-- First derivative of the concrete pair-distance quadratic form. -/
theorem fderiv_complexRadius (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (complexRadius n) z v = radiusBilinear n v z + radiusBilinear n z v := by
  have heq : complexRadius n = fun w : Configuration n =>
      (n : ℂ) * ∑ j, w j * conj (w j) - coordinateSum w * conj (coordinateSum w) := by
    funext w; exact complexRadius_eq n w
  have hcoord (j : Fin n) : Differentiable ℝ (fun w : Configuration n => w j) := by fun_prop
  have hconj (j : Fin n) : Differentiable ℝ (fun w : Configuration n => conj (w j)) := by fun_prop
  have hs : Differentiable ℝ (coordinateSum : Configuration n → ℂ) := by
    have he : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by funext w; simp
    rw [he]; fun_prop
  have hcs : Differentiable ℝ (fun w : Configuration n => conj (coordinateSum w)) :=
    Complex.conjCLE.differentiable.comp hs
  rw [heq, fderiv_fun_sub
    (f := fun w : Configuration n => (n : ℂ) * ∑ j, w j * conj (w j))
    (g := fun w : Configuration n => coordinateSum w * conj (coordinateSum w))
    (by fun_prop) ((hs z).mul (hcs z)),
    fderiv_const_mul (by fun_prop), fderiv_fun_sum]
  · simp only [sub_apply, sum_apply, smul_apply, smul_eq_mul]
    have hdp (j : Fin n) : fderiv ℝ (fun w : Configuration n => w j) z v = v j := by
      change fderiv ℝ (ContinuousLinearMap.proj j : Configuration n →L[ℝ] ℂ) z v = _
      rw [ContinuousLinearMap.fderiv]; rfl
    have hm (j : Fin n) :
        fderiv ℝ (fun w : Configuration n => w j * conj (w j)) z v =
          conj (z j) * v j + z j * conj (v j) := by
      rw [fderiv_fun_mul (hcoord j z) (hconj j z)]
      simp [fderiv_conj_coordinate, hdp, add_comm]
    rw [fderiv_fun_mul (hs z) (hcs z)]
    have hds : fderiv ℝ (coordinateSum : Configuration n → ℂ) z v = coordinateSum v := by
      have he : (coordinateSum : Configuration n → ℂ) = coordinateSumCLM n := by funext w; simp
      rw [he, ContinuousLinearMap.fderiv]
    simp [hm, hds, fderiv_conj_sum, radiusBilinear, Finset.sum_add_distrib,
      mul_comm]
    ring
  · intro j _; exact (hcoord j z).mul (hconj j z)

/-- Directional derivatives of the radius are continuous real-linear observables. -/
theorem radius_directional_eq (n : ℕ) (v : Configuration n) :
    (fun z => fderiv ℝ (complexRadius n) z v) =
      (radiusRightCLM n v + radiusLeftCLM n v : Configuration n →L[ℝ] ℂ) := by
  funext z
  simp [fderiv_complexRadius]

/-- Second directional derivative of the radius. -/
theorem second_complexRadius (n : ℕ) (v z : Configuration n) :
    complexSecondDirectionalDerivative (complexRadius n) v z = 2 * complexRadius n v := by
  unfold complexSecondDirectionalDerivative
  rw [radius_directional_eq, ContinuousLinearMap.fderiv]
  simp [complexRadius_eq]
  ring

/-- First derivative along a single complex particle direction. -/
theorem complexRadius_coordinateDirection (n : ℕ) (j : Fin n) (w : ℂ) (z : Configuration n) :
    fderiv ℝ (complexRadius n) z (coordinateDirection j w) =
      ((n : ℂ) * conj (z j) - conj (coordinateSum z)) * w +
        ((n : ℂ) * z j - coordinateSum z) * conj w := by
  simp [fderiv_complexRadius, radiusBilinear, coordinateDirection, coordinateSum,
    apply_ite, Finset.sum_ite_eq']
  ring

/-- The confinement part differentiates the quadratic radius with degree two. -/
theorem complexRadius_confinement (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n, fderiv ℝ (complexRadius n) z (coordinateDirection j (z j))) =
      2 * complexRadius n z := by
  have hs : (∑ j : Fin n, coordinateDirection j (z j)) = z := by
    funext k; simp [coordinateDirection]
  rw [← map_sum, hs, fderiv_complexRadius, complexRadius_eq]
  ring

/-- The singular pair drift differentiates the radius to the constant `2n`. -/
theorem complexRadius_coulomb (n : ℕ) (z : Configuration n) (hz : CollisionFree z)
    (j k : Fin n) (hjk : j < k) :
    fderiv ℝ (complexRadius n) z (coulombPairDirection j k z) = 2 * (n : ℂ) := by
  have hne : z j - z k ≠ 0 := sub_ne_zero.mpr (fun h => (ne_of_lt hjk) (hz h))
  have hnorm : (Complex.normSq (z j - z k) : ℂ) ≠ 0 := by
    exact_mod_cast (mt Complex.normSq_eq_zero.mp hne)
  rw [coulombPairDirection, map_sub, complexRadius_coordinateDirection,
    complexRadius_coordinateDirection]
  simp only [map_div₀, Complex.conj_ofReal]
  have hprod : (z j - z k) * conj (z j - z k) = (Complex.normSq (z j - z k) : ℂ) :=
    Complex.mul_conj _
  simp only [map_sub] at hprod ⊢
  field_simp
  linear_combination (2 * (n : ℂ)) * hprod

/-- Radius value on a real coordinate basis direction. -/
theorem complexRadius_realDirection (n : ℕ) (j : Fin n) :
    complexRadius n (realCoordinateDirection j) = (n : ℂ) - 1 := by
  simp [complexRadius_eq, radiusBilinear, realCoordinateDirection, coordinateDirection,
    coordinateSum, apply_ite, Finset.sum_ite_eq']

/-- Radius value on an imaginary coordinate basis direction. -/
theorem complexRadius_imaginaryDirection (n : ℕ) (j : Fin n) :
    complexRadius n (imaginaryCoordinateDirection j) = (n : ℂ) - 1 := by
  simp [complexRadius_eq, radiusBilinear, imaginaryCoordinateDirection, coordinateDirection,
    coordinateSum, apply_ite, Finset.sum_ite_eq', Complex.I_mul_I]

end
end GinibrePoincare
