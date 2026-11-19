/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibrePermutationAverage.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibrePermutationGradient

/-! # Finite permutation averaging for smooth Ginibre observables -/


@[expose] public section


open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- Average an observable over all particle permutations to obtain a symmetric observable. -/
def ginibrePermutationAverage {n : ℕ} (f : Configuration n → ℝ) :
    Configuration n → ℝ := fun z =>
  (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ *
    ∑ σ : ParticlePermutation n, f (permute σ z)

theorem ginibrePermutationAverage_symmetric {n : ℕ} (f : Configuration n → ℝ) :
    IsSymmetric (ginibrePermutationAverage f) := by
  intro τ z
  simp only [ginibrePermutationAverage]
  congr 1
  classical
  let e : ParticlePermutation n ≃ ParticlePermutation n :=
    Equiv.mulLeft τ
  have he (σ : ParticlePermutation n) (i : Fin n) :
      (τ * σ) i = τ (σ i) := rfl
  rw [← Equiv.sum_comp e (fun σ => f (permute σ z))]
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1

theorem ginibrePermutationAverage_smooth {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ginibrePermutationAverage f) := by
  unfold ginibrePermutationAverage
  apply contDiff_const.mul
  apply ContDiff.sum
  intro σ hσ
  have hp : ContDiff ℝ ∞ (permute σ : Configuration n → Configuration n) := by
    let P : Configuration n →L[ℝ] Configuration n :=
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm).toContinuousLinearMap
    have hP (z : Configuration n) : P z = permute σ z := by
      funext i
      simp [P, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply, permute]
    have hc : ContDiff ℝ ∞ P := P.contDiff
    have heq : (P : Configuration n → Configuration n) = permute σ := funext hP
    rw [← heq]
    exact hc
  exact hf.comp hp

/-- The Reynolds average of any smooth compact scalar observable is again
smooth, compactly supported, and symmetric. -/
theorem ginibrePermutationAverage_smoothCompact {n : ℕ}
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    IsSmoothCompactSymmetric (ginibrePermutationAverage f) := by
  refine ⟨ginibrePermutationAverage_smooth f hf, ?_, ginibrePermutationAverage_symmetric f⟩
  classical
  let e (σ : ParticlePermutation n) : Configuration n ≃L[ℝ] Configuration n :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm
  have he (σ : ParticlePermutation n) (z : Configuration n) : e σ z = permute σ z := by
    ext i
    simp [e, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply, permute]
  have hcomp (σ : ParticlePermutation n) :
      HasCompactSupport (fun z => f (permute σ z)) := by
    have hc := hfc.comp_homeomorph (e σ).toHomeomorph
    convert hc using 1
    funext z
    change f (permute σ z) = f (e σ z)
    rw [← he]
  convert (HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun σ z => f (permute σ z)) (fun σ _ => hcomp σ)).mul_left
        (f := fun _ => (Fintype.card (ParticlePermutation n) : ℝ)⁻¹) using 1
  funext z
  simp only [ginibrePermutationAverage, Pi.mul_apply, Finset.sum_apply]

/-- Differentiation commutes with the finite permutation average. -/
theorem fderiv_ginibrePermutationAverage {n : ℕ}
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z v : Configuration n) :
    fderiv ℝ (ginibrePermutationAverage f) z v =
      (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ *
        ∑ σ : ParticlePermutation n,
          fderiv ℝ (fun y => f (permute σ y)) z v := by
  have hperm (σ : ParticlePermutation n) :
      ContDiff ℝ ∞ (permute σ : Configuration n → Configuration n) := by
    let P : Configuration n →L[ℝ] Configuration n :=
      (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm).toContinuousLinearMap
    have hP (y : Configuration n) : P y = permute σ y := by
      funext i
      simp [P, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply, permute]
    have heq : (P : Configuration n → Configuration n) = permute σ := funext hP
    rw [← heq]
    exact P.contDiff
  have hsum : ContDiff ℝ ∞ (fun y => ∑ σ : ParticlePermutation n, f (permute σ y)) := by
    apply ContDiff.sum
    intro σ hσ
    exact hf.comp (hperm σ)
  unfold ginibrePermutationAverage
  change fderiv ℝ ((Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
      (fun y => ∑ σ : ParticlePermutation n, f (permute σ y))) z v = _
  have hdSum : DifferentiableAt ℝ
      (fun y => ∑ σ : ParticlePermutation n, f (permute σ y)) z :=
    (hsum.differentiable (by simp)).differentiableAt
  rw [fderiv_const_smul hdSum]
  rw [fderiv_fun_sum (u := Finset.univ)]
  · simp [smul_eq_mul]
  · intro σ hσ
    exact (hf.comp (hperm σ)).differentiable (by simp) |>.differentiableAt

/-- The actual Euclidean gradient commutes with finite permutation averaging. -/
theorem ginibreEuclideanGradient_permutationAverage {n : ℕ}
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    ginibreEuclideanGradient (ginibrePermutationAverage f) z =
      (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
        ∑ σ : ParticlePermutation n,
          ginibreEuclideanGradient (fun y => f (permute σ y)) z := by
  apply PiLp.ext
  intro k
  rw [ginibreEuclideanGradient_coordinate, fderiv_ginibrePermutationAverage f hf z
    (ginibreCoordinateDirection k)]
  simp only [ginibreEuclideanGradient, PiLp.smul_apply, smul_eq_mul
    ]
  by_cases hk : k.2 = 0
  · simp [ginibreCoordinateDirection, hk]
  · simp [ginibreCoordinateDirection, hk]

/-- The same averaging formula expressed directly as coordinate permutation of
the original gradient at the relabelled configuration. -/
theorem ginibreEuclideanGradient_permutationAverage_covariant {n : ℕ}
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    ginibreEuclideanGradient (ginibrePermutationAverage f) z =
      (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
        ∑ σ : ParticlePermutation n,
          WithLp.toLp 2 (fun k : Fin n × Fin 2 =>
            ginibreEuclideanGradient f (permute σ z) (σ.symm k.1, k.2)) := by
  rw [ginibreEuclideanGradient_permutationAverage f hf z]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  exact ginibreEuclideanGradient_comp_permute σ f hf z

end
end GinibrePoincare
