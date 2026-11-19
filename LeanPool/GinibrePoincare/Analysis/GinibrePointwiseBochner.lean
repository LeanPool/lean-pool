/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePointwiseBochner.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePointwiseBochnerFormula
public import LeanPool.GinibrePoincare.Analysis.GinibreGeneratorGradientCommutation

/-!
# Ginibre pointwise Bochner

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibrePointwiseGammaTwo_eq_iterated`, `ginibrePointwiseGammaTwo_bochner_bilinear`.
-/

@[expose] public section
open scoped ContDiff BigOperators Topology
open Filter
namespace GinibrePoincare
noncomputable section

/-- The carré du champ of the actual Ginibre generator. -/
def ginibrePointwiseGamma (n : ℕ) (f g : Configuration n → ℝ) (z : Configuration n) : ℝ :=
 (ginibrePregenerator n (fun y => f y*g y) z-f z*ginibrePregenerator n g z-g z*ginibrePregenerator n
     f z)/2

/-- The actual iterated carré du champ, with its differential cross term. -/
def ginibrePointwiseGammaTwo (n : ℕ) (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
 ginibrePregenerator n (fun y => (1/(n : ℝ))*∑ i : Fin n×Fin 2,
   (bochnerDirectionalDerivative (ginibreBochnerDirection i) f y)^2) z/2-
 (1/(n : ℝ))*∑ i : Fin n×Fin 2, bochnerDirectionalDerivative (ginibreBochnerDirection i) f z*
   bochnerDirectionalDerivative (ginibreBochnerDirection i) (ginibrePregenerator n f) z

theorem ginibrePointwiseGamma_eq {n : ℕ} (hn : 0 < n) (f g : Configuration n → ℝ)
 (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : Configuration n) (hz : CollisionFree z) :
 ginibrePointwiseGamma n f g z=(1/(n : ℝ))*∑ i : Fin n×Fin 2,
   bochnerDirectionalDerivative (ginibreBochnerDirection i) f z*bochnerDirectionalDerivative
       (ginibreBochnerDirection i) g z := by
 unfold ginibrePointwiseGamma
 simp_rw [ginibrePregenerator_eq_bochnerCoordinateOperator hn _ z hz]
 exact bochnerGamma_eq _ _ _ f g z hf hg

theorem ginibrePointwiseGamma_eq_at {n : ℕ} (hn : 0 < n) (f g : Configuration n → ℝ)
 (z : Configuration n) (hz : CollisionFree z)
 (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
 ginibrePointwiseGamma n f g z=(1/(n : ℝ))*∑ i : Fin n×Fin 2,
   bochnerDirectionalDerivative (ginibreBochnerDirection i) f z*bochnerDirectionalDerivative
       (ginibreBochnerDirection i) g z := by
 unfold ginibrePointwiseGamma
 simp_rw [ginibrePregenerator_eq_bochnerCoordinateOperator hn _ z hz]
 rw [bochnerCoordinateOperator_mul_at _ _ _ f g z hf hg]
 ring

theorem ginibrePregenerator_contDiffAt_of_contDiff {n : ℕ} (hn : 0 < n)
 (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
 ContDiffAt ℝ ∞ (ginibrePregenerator n f) z := by
 have he : ginibrePregenerator n f =ᶠ[𝓝 z]
      bochnerCoordinateOperator ginibreBochnerDirection (1/(n : ℝ)) (ginibreBochnerDrift n) f := by
  filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with y hy
  exact ginibrePregenerator_eq_bochnerCoordinateOperator hn f y hy
 apply ContDiffAt.congr_of_eventuallyEq _ he
 unfold bochnerCoordinateOperator
 have hs1 : ContDiffAt ℝ ∞ (fun y => ∑ i : Fin n×Fin 2, bochnerDirectionalDerivative
     (ginibreBochnerDirection i)
    (bochnerDirectionalDerivative (ginibreBochnerDirection i) f) y) z := by
  exact ContDiffAt.sum (fun i _ => (bochnerDirectionalDerivative_contDiff _ _
    (bochnerDirectionalDerivative_contDiff _ f hf)).contDiffAt)
 have hs2 : ContDiffAt ℝ ∞ (fun y => ∑ i : Fin n×Fin 2, ginibreBochnerDrift n i y*
    bochnerDirectionalDerivative (ginibreBochnerDirection i) f y) z := by
  refine ContDiffAt.sum (fun i _ => ?_)
  exact (contDiffAt_const.mul (bochnerDirectionalDerivative_contDiffAt _ _ z
      (ginibreHamiltonian_contDiffAt n z hz))).mul
    (bochnerDirectionalDerivative_contDiff _ f hf).contDiffAt
 exact (contDiffAt_const.mul hs1).sub hs2

/-- Agreement with the operator-defined iterated carré du champ; no differential identity is
assumed. -/
theorem ginibrePointwiseGammaTwo_eq_iterated {n : ℕ} (hn : 0 < n)
 (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
 ginibrePointwiseGammaTwo n f z=
 ginibrePregenerator n (ginibrePointwiseGamma n f f) z/2-
 ginibrePointwiseGamma n f (ginibrePregenerator n f) z := by
 have he : ginibrePointwiseGamma n f f =ᶠ[𝓝 z] (fun y => (1/(n : ℝ))*∑ i : Fin n×Fin 2,
   (bochnerDirectionalDerivative (ginibreBochnerDirection i) f y)^2) := by
  filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with y hy
  simpa only [pow_two] using ginibrePointwiseGamma_eq hn f f hf hf y hy
 have he' : ginibrePregenerator n (ginibrePointwiseGamma n f f) z=
  ginibrePregenerator n (fun y => (1/(n : ℝ))*∑ i : Fin n×Fin 2,
   (bochnerDirectionalDerivative (ginibreBochnerDirection i) f y)^2) z := by
  simp_rw [ginibrePregenerator_eq_bochnerCoordinateOperator hn _ z hz]
  unfold bochnerCoordinateOperator bochnerDirectionalDerivative
  rw [he.fderiv_eq]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hd : (fun y => fderiv ℝ (ginibrePointwiseGamma n f f) y (ginibreBochnerDirection i)) =ᶠ[𝓝 z]
    (fun y => fderiv ℝ (fun y => (1/(n : ℝ))*∑ i : Fin n×Fin 2,
       (bochnerDirectionalDerivative (ginibreBochnerDirection i) f y)^2) y (ginibreBochnerDirection
           i)) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun a : Configuration n →L[ℝ] ℝ => a (ginibreBochnerDirection i)) hy
  exact congrArg (fun a : Configuration n →L[ℝ] ℝ => a (ginibreBochnerDirection i)) (hd.fderiv_eq (𝕜
      := ℝ))
 rw [he', ginibrePointwiseGamma_eq_at hn f (ginibrePregenerator n f) z hz hf.contDiffAt
   (ginibrePregenerator_contDiffAt_of_contDiff hn f hf z hz)]
 rfl

/-- Pointwise Bochner formula: the true Hessian square plus the true Hamiltonian Hessian
contraction. -/
theorem ginibrePointwiseGammaTwo_bochner {n : ℕ} (hn : 0 < n)
 (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
 ginibrePointwiseGammaTwo n f z=(1/(n : ℝ))^2*((∑ i : Fin n×Fin 2, ∑ j : Fin n×Fin 2,
   (fderiv ℝ (fderiv ℝ f) z (ginibreBochnerDirection j) (ginibreBochnerDirection i))^2)+
 (∑ i : Fin n×Fin 2, ∑ j : Fin n×Fin 2,
   bochnerDirectionalDerivative (ginibreBochnerDirection i) f z*
   fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z (ginibreBochnerDirection i) (ginibreBochnerDirection
       j)*
   bochnerDirectionalDerivative (ginibreBochnerDirection j) f z)) := by
 have he : ginibrePregenerator n f =ᶠ[𝓝 z]
      bochnerCoordinateOperator ginibreBochnerDirection (1/(n : ℝ)) (ginibreBochnerDrift n) f := by
  filter_upwards [(isOpen_collisionFree n).mem_nhds hz] with y hy
  exact ginibrePregenerator_eq_bochnerCoordinateOperator hn f y hy
 have hder i : bochnerDirectionalDerivative (ginibreBochnerDirection i) (ginibrePregenerator n f) z=
   bochnerDirectionalDerivative (ginibreBochnerDirection i)
     (bochnerCoordinateOperator ginibreBochnerDirection (1/(n : ℝ)) (ginibreBochnerDrift n) f) z :=
         by
  unfold bochnerDirectionalDerivative
  rw [he.fderiv_eq]
 unfold ginibrePointwiseGammaTwo
 rw [ginibrePregenerator_eq_bochnerCoordinateOperator hn _ z hz]
 simp_rw [hder]
 change bochnerGammaTwo _ _ _ f z=_
 rw [bochnerGammaTwo_eq _ _ _ f z hf (fun i => ginibreBochnerDrift_differentiableAt i z hz)]
 have hb i j : bochnerDirectionalDerivative (ginibreBochnerDirection i) (ginibreBochnerDrift n j) z=
  (1/(n : ℝ))*fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z (ginibreBochnerDirection i)
      (ginibreBochnerDirection j) := by
  unfold ginibreBochnerDrift
  rw [bochnerDirectionalDerivative_const_mul _ _ _ _
    ((bochnerDirectionalDerivative_contDiffAt _ _ _ (ginibreHamiltonian_contDiffAt n z
        hz)).differentiableAt (by simp)),
    bochnerDirectionalDerivative_iterated _ _ _ _ (ginibreHamiltonian_contDiffAt n z hz)]
 simp_rw [hb, bochnerDirectionalDerivative_iterated _ _ f z hf.contDiffAt]
 simp only [mul_assoc, ← Finset.mul_sum]
 ring_nf
 simp only [mul_assoc, ← Finset.mul_sum]
 ring

/-- The genuine Euclidean gradient expanded in the orthonormal real coordinate basis. -/
def ginibreBochnerGradient {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) : Configuration n
    :=
 ∑ i : Fin n×Fin 2, bochnerDirectionalDerivative (ginibreBochnerDirection i) f z •
     ginibreBochnerDirection i

/-- The squared Hilbert–Schmidt norm of the Hessian of `f` at `z` in the real coordinate
directions. -/
def ginibreBochnerHessianSquare {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
 ∑ i : Fin n×Fin 2, ∑ j : Fin n×Fin 2,
   (fderiv ℝ (fderiv ℝ f) z (ginibreBochnerDirection j) (ginibreBochnerDirection i))^2

/-- The paper's pointwise Bochner formula as a bilinear Hessian contraction. -/
theorem ginibrePointwiseGammaTwo_bochner_bilinear {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n)
    (hz : CollisionFree z) :
    (n : ℝ) ^ 2 * ginibrePointwiseGammaTwo n f z = ginibreBochnerHessianSquare f z +
      fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z (ginibreBochnerGradient f z)
        (ginibreBochnerGradient f z) := by
  have hcon : fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z (ginibreBochnerGradient f z)
      (ginibreBochnerGradient f z) =
      ∑ i : Fin n × Fin 2, ∑ j : Fin n × Fin 2,
        bochnerDirectionalDerivative (ginibreBochnerDirection i) f z *
        fderiv ℝ (fderiv ℝ (ginibreHamiltonian n)) z (ginibreBochnerDirection i)
          (ginibreBochnerDirection j) *
        bochnerDirectionalDerivative (ginibreBochnerDirection j) f z := by
    unfold ginibreBochnerGradient
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [((ginibreHamiltonian_contDiffAt n z hz).isSymmSndFDerivAt (by simp)).eq
      (ginibreBochnerDirection j) (ginibreBochnerDirection i)]
    ring
  rw [ginibrePointwiseGammaTwo_bochner hn f hf z hz, hcon]
  unfold ginibreBochnerHessianSquare
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

end
end GinibrePoincare
