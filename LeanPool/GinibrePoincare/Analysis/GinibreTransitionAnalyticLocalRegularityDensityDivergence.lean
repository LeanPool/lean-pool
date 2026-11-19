/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticLocalRegularityDensityDivergence.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityTestIntegrability
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradient

/-!
# Ginibre transition analytic local regularity density divergence

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreLocalRegularity_density_generator_pointwise`.
-/

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_density_generator_pointwise
    (n : ℕ) (hn : 0 < n) (θ : Configuration n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (z : Configuration n) (hz : CollisionFree z) :
    (n : ℝ)*ginibreLebesgueDensityReal n z*ginibrePregenerator n θ z =
      ginibreLebesgueDensityReal n z*(∑ k : Fin n × Fin 2,
        fderiv ℝ (fun y => fderiv ℝ θ y (ginibreCoordinateDirection k)) z
            (ginibreCoordinateDirection k)) +
      ∑ k : Fin n × Fin 2, fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)*
        fderiv ℝ θ z (ginibreCoordinateDirection k) := by
  have hprod (v : Configuration n) :
      fderiv ℝ (fun y => ginibreLebesgueDensityReal n y*fderiv ℝ θ y v) z v =
      ginibreLebesgueDensityReal n z*fderiv ℝ (fun y => fderiv ℝ θ y v) z v +
        fderiv ℝ (ginibreLebesgueDensityReal n) z v*fderiv ℝ θ z v := by
    have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ θ y v) :=
      (hθ.fderiv_right (by simp)).clm_apply contDiff_const
    change fderiv ℝ ((ginibreLebesgueDensityReal n)*(fun y => fderiv ℝ θ y v)) z v = _
    rw [fderiv_mul ((contDiff_ginibreLebesgueDensityReal n).differentiable (by simp) z)
      (hd.differentiable (by simp) z)]
    simp only [smul_apply, add_apply, smul_eq_mul]
    ring
  have he := ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence hn θ hθ z hz
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn0] at he
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, ginibreCoordinateDirection, ite_true, ite_false, one_ne_zero]
  simp_rw [hprod] at he
  rw [show (n : ℝ)*ginibreLebesgueDensityReal n z*ginibrePregenerator n θ z =
      ginibreLebesgueDensityReal n z*ginibrePregenerator n θ z*(n : ℝ) by ring, he, Finset.mul_sum,←
                                                                            Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end GinibrePoincare
