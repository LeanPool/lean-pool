/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticGeneratorNormalization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactTaylorMeasurability
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGenerator
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianDrift

/-! The genuine Itô correction has exactly the paper's implemented generator. -/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem ginibreLangevin_fderiv_generator {n : ℕ} (hn : 0 < n) (α : ℝ)
    (f : Configuration n → ℝ) (z : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ f z (ginibreLangevinDrift n α z)+
      (α/(n : ℝ)^2)*configurationLaplacian f z =
      ginibreRealPaperSpeedGenerator n α f z := by
  rw [ginibreConfiguration_fderiv_coordinate_sum]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  change (∑ j : Fin n, ((ginibreLangevinDrift n α z j).re*fderiv ℝ f z (realCoordinateDirection j)+
    (ginibreLangevinDrift n α z j).im*fderiv ℝ f z (imaginaryCoordinateDirection j)))+
      (α/(n : ℝ)^2)*configurationLaplacian f z = ginibreRealPaperSpeedGenerator n α f z
  simp_rw [ginibreLangevinDrift_re_hamiltonian hn α z hz,
    ginibreLangevinDrift_im_hamiltonian hn α z hz,
    fderiv_ginibreHamiltonian_realCoordinate hn z hz,
    fderiv_ginibreHamiltonian_imaginaryCoordinate hn z hz]
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_eq_laplacian_sub_drift]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [mul_sub]
  have he : ∑ j : Fin n,
      (-(α/(n : ℝ)^2)*((n : ℝ)*ginibreRealDriftCoordinate n j z)*
          fderiv ℝ f z (realCoordinateDirection j)+
        -(α/(n : ℝ)^2)*((n : ℝ)*ginibreImagDriftCoordinate n j z)*
          fderiv ℝ f z (imaginaryCoordinateDirection j)) =
      -(α/(n : ℝ))*∑ j : Fin n,
        (ginibreRealDriftCoordinate n j z*fderiv ℝ f z (realCoordinateDirection j)+
          ginibreImagDriftCoordinate n j z*fderiv ℝ f z (imaginaryCoordinateDirection j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hne]
    ring
  rw [he]
  field_simp [hne]
  ring
end
end GinibrePoincare
