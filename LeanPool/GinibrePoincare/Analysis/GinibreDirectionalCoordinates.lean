/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDirectionalCoordinates.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalGradient

/-! # Arbitrary real directions in Ginibre configuration space

The real and imaginary coordinate directions decompose every configuration
vector. This provides the directional calculus needed for rotating weak tests.
-/


@[expose] public section


open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- Real coordinates of a configuration vector, indexed like the actual gradient. -/
def ginibreDirectionCoefficient {n : ℕ} (v : Configuration n) (k : Fin n × Fin 2) : ℝ :=
  if k.2 = 0 then (v k.1).re else (v k.1).im

/-- Every real direction is the finite sum of its actual coordinate components. -/
theorem ginibreDirection_decomposition {n : ℕ} (v : Configuration n) :
    (∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k • ginibreCoordinateDirection k) = v := by
  classical
  ext i ; simp [Fintype.sum_prod_type, Fin.sum_univ_two, ginibreDirectionCoefficient,
    ginibreCoordinateDirection, realCoordinateDirection, imaginaryCoordinateDirection,
    coordinateDirection, Complex.real_smul, Finset.sum_add_distrib]

/-- Any real Fréchet directional derivative is its finite coordinate pairing. -/
theorem fderiv_ginibreDirection_decomposition {n : ℕ} (f : Configuration n → ℝ)
    (z v : Configuration n) :
    fderiv ℝ f z v = ∑ k : Fin n × Fin 2,
      ginibreDirectionCoefficient v k * fderiv ℝ f z (ginibreCoordinateDirection k) := by
  calc
    _ = fderiv ℝ f z (∑ k : Fin n × Fin 2,
        ginibreDirectionCoefficient v k • ginibreCoordinateDirection k) := by
      rw [ginibreDirection_decomposition]
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

/-- The independently defined ordinary weak-gradient identity holds in every
real configuration direction, not just in coordinate directions. -/
theorem ginibre_distributional_gradient_directional (n : ℕ)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (v : Configuration n) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    (∫ z, (∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k * g z k) * θ z) =
      -(∫ z, u z * fderiv ℝ θ z v) := by
  classical
  have hi (k : Fin n × Fin 2) : Integrable (fun z => g z k * θ z) :=
    integrable_mul_collisionFree_test _ θ (hg.2.1 k) hθ.continuous hc hs
  have hj (k : Fin n × Fin 2) : Integrable
      (fun z => u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) :=
    integrable_mul_collisionFree_test _ _ hg.1
      ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have hr : (∫ z, u z * fderiv ℝ θ z v) =
      ∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k *
        (∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
    calc
      _ = ∫ z, ∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k *
          (u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        dsimp only
        rw [fderiv_ginibreDirection_decomposition, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [integral_finsetSum Finset.univ (fun k _ => (hj k).const_mul _)]
        simp only [integral_const_mul]
  calc
    _ = ∫ z, ∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k * (g z k * θ z) := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      simp only [Finset.sum_mul, mul_assoc]
    _ = ∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k * (∫ z, g z k * θ z) := by
      rw [integral_finsetSum Finset.univ (fun k _ => (hi k).const_mul _)]
      simp only [integral_const_mul]
    _ = ∑ k : Fin n × Fin 2, ginibreDirectionCoefficient v k *
        (-(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hg.2.2 k θ hθ hc hs]
    _ = _ := by rw [hr]; simp only [mul_neg, Finset.sum_neg_distrib]

end
end GinibrePoincare
