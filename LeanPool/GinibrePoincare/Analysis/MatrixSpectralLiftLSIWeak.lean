/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralLiftLSIWeak.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftEntryLp
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftFullEntry
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevSpectralWeak
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevWeakDomain

/-!
# Matrix spectral lift LSI weak

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixSpectralLift_ordinary_weak_lsi`.

The two weak-derivative bridges `matrixSpectralLift_ordinary_weak_pair` and
`matrixSpectralLift_finite_overlap_weak_pair` are shared by the entropy route here and the
variance route of `AlternativeMatrixPoincare`.
-/

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- An ordinary weak entry pair representing a spectral lift and its intrinsic gradient
transports to a matrix H¹ pair whose value and coordinate gradient represent the matrix
lift and its coordinate derivatives almost everywhere. -/
theorem matrixSpectralLift_ordinary_weak_pair {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ)
    (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
    (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 (matrixEntryGaussianMeasure e))
    (hu : (u : Configuration m → ℝ) =ᵐ[matrixEntryGaussianMeasure e]
      (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)))
    (hg : (g : Configuration m → EuclideanSpace ℝ (Fin m × Fin 2)) =ᵐ[matrixEntryGaussianMeasure e]
      matrixEntryIntrinsicSpectralGradient e F)
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    let q : MatrixGaussianSobolevPair n := (matrixEntryL2ToMatrix hn e u,
      fun i => matrixEntryL2ToMatrix hn e
        ((configurationGradientComponent m ((matrixEntryRealIndexEquiv e).symm i)).compLpL
          2 (matrixEntryGaussianMeasure e) g))
    q ∈ matrixGaussianH1Completion n ∧
      (q.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F ∧
      ∀ i, (q.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
        (fun A => fderiv ℝ (matrixSymmetricLift n F) A
          (matrixRealCoordinates n (Pi.single i 1))) := by
  intro q
  have hpres :=
    (matrixComplexEntryEquiv_gaussian_preserving hn e).symm (matrixEntryMeasurableEquiv e)
  refine ⟨matrixEntry_full_weak_pair_mem_H1Completion hn e u g hweak, ?_, ?_⟩
  · filter_upwards [matrixEntryL2ToMatrix_ae hn e u, hpres.quasiMeasurePreserving.ae hu]
      with A hA hB
    change u ((matrixComplexEntryEquiv e).symm A) =
      matrixSymmetricLift n F (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A)) at hB
    rw [(matrixComplexEntryEquiv e).apply_symm_apply A] at hB
    exact hA.trans hB
  intro i
  let j := (matrixEntryRealIndexEquiv e).symm i
  have hc := (configurationGradientComponent m j).coeFn_compLpL g
  filter_upwards [matrixEntryL2ToMatrix_ae hn e ((configurationGradientComponent m j).compLpL
    2 (matrixEntryGaussianMeasure e) g), hpres.quasiMeasurePreserving.ae hc,
    hpres.quasiMeasurePreserving.ae hg] with A hA hB hC
  change ((configurationGradientComponent m j).compLpL 2 (matrixEntryGaussianMeasure e) g)
    ((matrixComplexEntryEquiv e).symm A) = g ((matrixComplexEntryEquiv e).symm A) j at hB
  change g ((matrixComplexEntryEquiv e).symm A) =
    matrixEntryIntrinsicSpectralGradient e F ((matrixComplexEntryEquiv e).symm A) at hC
  rw [hA, hB]
  have hCj := congrArg (fun v : EuclideanSpace ℝ (Fin m × Fin 2) => v j) hC
  rw [hCj]
  change fderiv ℝ (matrixSymmetricLift n F)
    (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A))
    (matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e j) 1)) = _
  rw [(matrixComplexEntryEquiv e).apply_symm_apply A, Equiv.apply_symm_apply]

/-- Finite actual overlap energy yields ordinary weak entry representatives of a spectral
lift and its intrinsic gradient: the weak derivative equations hold through all collision
matrices by the coordinate-line removability argument. -/
theorem matrixSpectralLift_finite_overlap_weak_pair {n d : ℕ} (hn : 0 < n)
    (e : Fin (d + 1) ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    ∃ (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
      (g : Lp (EuclideanSpace ℝ (Fin (d + 1) × Fin 2)) 2 (matrixEntryGaussianMeasure e)),
      (u : Configuration (d + 1) → ℝ) =ᵐ[matrixEntryGaussianMeasure e]
          (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)) ∧
        (g : Configuration (d + 1) → EuclideanSpace ℝ (Fin (d + 1) × Fin 2))
          =ᵐ[matrixEntryGaussianMeasure e] matrixEntryIntrinsicSpectralGradient e F ∧
        ∀ i : Fin (d + 1) × Fin 2, ∀ θ : Configuration (d + 1) → ℝ,
          ContDiff ℝ ∞ θ → HasCompactSupport θ →
          (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i)) := by
  let V := fun x : Configuration (d+1) => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)
  have hV : MemLp V 2 (matrixEntryGaussianMeasure e) :=
    matrixEntryIntrinsicSpectralValue_memLp hn e F hF.continuous.measurable hsym hFL2
  have hG := matrixEntryIntrinsicSpectralGradient_memLp hn e F hF hsym hE
  let u : Lp ℝ 2 (matrixEntryGaussianMeasure e) := hV.toLp V
  let g : Lp (EuclideanSpace ℝ (Fin (d+1) × Fin 2)) 2 (matrixEntryGaussianMeasure e) :=
    hG.toLp (matrixEntryIntrinsicSpectralGradient e F)
  have hu : (u : Configuration (d+1) → ℝ) =ᵐ[matrixEntryGaussianMeasure e] V := hV.coeFn_toLp
  have hg : (g : Configuration (d+1) → EuclideanSpace ℝ (Fin (d+1) × Fin 2))
      =ᵐ[matrixEntryGaussianMeasure e] matrixEntryIntrinsicSpectralGradient e F := hG.coeFn_toLp
  have hFull : matrixEntryFullSpectralLift e F =ᵐ[matrixEntryGaussianMeasure e] V := by
    filter_upwards [(matrixComplexEntryEquiv_gaussian_preserving hn e).quasiMeasurePreserving.ae
      (matrixFullSymmetricSpectralLift_eq_ae n F hsym)] with x hx
    exact hx
  have huVol : (u : Configuration (d+1) → ℝ) =ᵐ[volume] matrixEntryFullSpectralLift e F :=
    (matrixEntryGaussian_ae_iff_volume hn e _).mp (hu.trans hFull.symm)
  refine ⟨u, g, hu, hg, ?_⟩
  intro i θ hθ hc
  have hgScalar : (fun x => g x i) =ᵐ[matrixEntryGaussianMeasure e]
      (fun x => matrixEntryIntrinsicSpectralGradient e F x i) := by
    filter_upwards [hg] with x hx
    exact congrArg (fun v : EuclideanSpace ℝ (Fin (d+1) × Fin 2) => v i) hx
  have hder := matrixEntryFullSpectralLift_derivative_ae hn e F hF hsym i
  have hgVol : (fun x => g x i) =ᵐ[volume]
      (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i)) :=
    (matrixEntryGaussian_ae_iff_volume hn e _).mp (hgScalar.trans hder.symm)
  have ht := matrixFullSpectralLift_coordinate_weak_test n d e F hF hsym i
    (matrixEntryFullSpectralLift_derivative_locallyIntegrable hn e F hF hsym hE i) θ hθ hc
  calc
    _ = ∫ x, fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i) * θ x :=
        by
      apply integral_congr_ae
      filter_upwards [hgVol] with x hx
      exact congrArg (fun v : ℝ => v * θ x) hx
    _ = -(∫ x, matrixEntryFullSpectralLift e F x * fderiv ℝ θ x (ginibreCoordinateDirection i)) :=
        ht
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [huVol] with x hx
      exact congrArg (fun v : ℝ => v * fderiv ℝ θ x (ginibreCoordinateDirection i)) hx.symm

/-- Ordinary volume weak derivatives of actual intrinsic entry representatives
produce the sharp Ginibre matrix-overlap LSI through the proved matrix H1 domain.
This intermediate theorem assumes no inequality or graph-membership conclusion. -/
theorem matrixSpectralLift_ordinary_weak_lsi {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
    (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 (matrixEntryGaussianMeasure e))
    (hu : (u : Configuration m → ℝ) =ᵐ[matrixEntryGaussianMeasure e]
      (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)))
    (hg : (g : Configuration m → EuclideanSpace ℝ (Fin m × Fin 2)) =ᵐ[matrixEntryGaussianMeasure e]
      matrixEntryIntrinsicSpectralGradient e F)
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) F ≤
        (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  obtain ⟨hq, hv, hd⟩ := matrixSpectralLift_ordinary_weak_pair hn e F u g hu hg hweak
  exact matrixSpectralLift_H1_lsi hn F hF hsym _ hq hv hd

end
end GinibrePoincare
