/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianCoercivity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianCollision
public import LeanPool.GinibrePoincare.Analysis.GinibreDensityBound
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure

/-! A genuine quadratic lower bound for the Hamiltonian, including repulsion. -/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The constant `n² (log (8 n) - 1) + n / 2` used in the lower bound for the Ginibre
Hamiltonian. -/
def ginibreHamiltonianLowerBoundConstant (n : ℕ) : ℝ :=
  (n : ℝ)^2 * (Real.log (8*(n : ℝ))-1) + (n : ℝ)/2

theorem ginibreHamiltonian_quadratic_lower_bound {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    (n : ℝ)/2*configurationNormSq z - ginibreHamiltonianLowerBoundConstant n ≤
      ginibreHamiltonian n z := by
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hS := configurationNormSq_nonneg z
  have hp : 0 < (configurationNormSq z+1)/(2*(n : ℝ)) :=
    div_pos (by linarith) (by positivity)
  have hlog := Real.log_le_sub_one_of_pos hp
  have hprod : 4*(configurationNormSq z+1) =
      (8*(n : ℝ))*((configurationNormSq z+1)/(2*(n : ℝ))) := by
    field_simp
    ring
  have hL : Real.log (4*(configurationNormSq z+1)) ≤
      Real.log (8*(n : ℝ)) + (configurationNormSq z+1)/(2*(n : ℝ))-1 := by
    rw [hprod, Real.log_mul (by positivity) (ne_of_gt hp)]
    linarith
  have hW := Real.log_le_log (vandermondeWeight_pos_of_collisionFree z hz)
    (vandermondeWeight_le_radius_bound n z)
  rw [Real.log_pow] at hW
  have hD : ((n*n : ℕ) : ℝ) = (n : ℝ)^2 := by push_cast; ring
  rw [hD] at hW
  have hB := mul_le_mul_of_nonneg_left hL (sq_nonneg (n : ℝ))
  have hcalc : (n : ℝ)^2 *
      (Real.log (8*(n : ℝ))+(configurationNormSq z+1)/(2*(n : ℝ))-1) =
      (n : ℝ)/2*configurationNormSq z + ginibreHamiltonianLowerBoundConstant n := by
    unfold ginibreHamiltonianLowerBoundConstant
    field_simp
    ring
  rw [hcalc] at hB
  unfold ginibreHamiltonian
  linarith

theorem ginibreHamiltonian_bounded_below {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    -ginibreHamiltonianLowerBoundConstant n ≤ ginibreHamiltonian n z := by
  have h := ginibreHamiltonian_quadratic_lower_bound hn z hz
  have hN : 0 ≤ (n : ℝ)/2 := by positivity
  have hs := mul_nonneg hN (configurationNormSq_nonneg z)
  linarith

end
end GinibrePoincare
