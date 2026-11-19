/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreGeneratorGradientCommutation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochnerOperator
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGenerator

/-!
# Ginibre generator gradient commutation

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibrePregenerator_gradient_commutation`.
-/

@[expose] public section
open scoped ContDiff BigOperators Topology
open Filter Set
namespace GinibrePoincare
noncomputable section

/-- The real coordinate direction indexed by a particle and its real or imaginary component. -/
def ginibreBochnerDirection {n : ℕ} (i : Fin n × Fin 2) : Configuration n :=
  if i.2=0 then realCoordinateDirection i.1 else imaginaryCoordinateDirection i.1

/-- The drift component `(1 / n) ∂_i H` of the Ginibre Hamiltonian `H` along the real
coordinate direction `i`. -/
def ginibreBochnerDrift (n : ℕ) (i : Fin n × Fin 2) (z : Configuration n) : ℝ :=
  (1/(n : ℝ))*bochnerDirectionalDerivative (ginibreBochnerDirection i) (ginibreHamiltonian n) z

theorem ginibrePregenerator_eq_bochnerCoordinateOperator {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibrePregenerator n f z=bochnerCoordinateOperator ginibreBochnerDirection
      (1/(n : ℝ)) (ginibreBochnerDrift n) f z := by
  rw [ginibrePregenerator_eq_laplacian_sub_drift]
  unfold bochnerCoordinateOperator ginibreBochnerDrift configurationLaplacian
  have hne : (n : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, ginibreBochnerDirection,
    bochnerDirectionalDerivative, secondDirectionalDerivative,
    fderiv_ginibreHamiltonian_realCoordinate hn z hz,
    fderiv_ginibreHamiltonian_imaginaryCoordinate hn z hz, hne]
  rfl

theorem ginibreBochnerDrift_differentiableAt {n : ℕ} (i : Fin n × Fin 2)
    (z : Configuration n) (hz : CollisionFree z) :
    DifferentiableAt ℝ (ginibreBochnerDrift n i) z := by
  exact ((bochnerDirectionalDerivative_contDiffAt (ginibreBochnerDirection i)
    (ginibreHamiltonian n) z (ginibreHamiltonian_contDiffAt n z hz)).differentiableAt
      (by simp)).const_mul _

theorem ginibrePregenerator_gradient_commutation {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f)
    (z u : Configuration n) (hz : CollisionFree z) :
    bochnerDirectionalDerivative u (ginibrePregenerator n f) z=
      ginibrePregenerator n (bochnerDirectionalDerivative u f) z-
        (1/(n : ℝ))*∑ i : Fin n×Fin 2,
          (fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z u (ginibreBochnerDirection i))*
            bochnerDirectionalDerivative (ginibreBochnerDirection i) f z := by
  have he : ginibrePregenerator n f =ᶠ[𝓝 z]
      bochnerCoordinateOperator ginibreBochnerDirection (1/(n : ℝ)) (ginibreBochnerDrift n) f := by
    filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with y hy
    exact ginibrePregenerator_eq_bochnerCoordinateOperator hn f y hy
  unfold bochnerDirectionalDerivative at he ⊢
  rw [he.fderiv_eq]
  change bochnerDirectionalDerivative u
      (bochnerCoordinateOperator ginibreBochnerDirection (1/(n : ℝ)) (ginibreBochnerDrift n) f) z=_
  rw [bochnerCoordinateOperator_directional_commutation _ _ _ _ _ _ hf
    (fun i => ginibreBochnerDrift_differentiableAt i z hz),
    ← ginibrePregenerator_eq_bochnerCoordinateOperator hn _ z hz]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold ginibreBochnerDrift
  rw [bochnerDirectionalDerivative_const_mul _ _ _ _
    ((bochnerDirectionalDerivative_contDiffAt _ _ _ (ginibreHamiltonian_contDiffAt n z
        hz)).differentiableAt (by simp)),
    bochnerDirectionalDerivative_iterated _ _ _ _ (ginibreHamiltonian_contDiffAt n z hz)]
  simp only [bochnerDirectionalDerivative]
  ring

end
end GinibrePoincare
