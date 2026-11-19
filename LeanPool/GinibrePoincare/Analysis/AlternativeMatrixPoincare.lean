/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeMatrixPoincare.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianPoincare
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftLSITransport
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftFullEntry
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevSpectralWeak
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralLiftEntryLp
public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevWeakDomain

/-! # The Gaussian matrix route to the overlap variance inequality

Theorem 1.13: spectral pushforward, actual Gaussian matrix Poincaré inequality,
and the exact entry-gradient/overlap identity. The Ginibre Poincaré inequality
and the overlap lower-bound comparison are not invoked.

The first endpoint starts from a Gaussian H¹ pair, transports its variance to
Ginibre eigenvalues, and converts its entry-gradient energy to four times the
overlap energy. The Gaussian constant `1 / (2 * n)` therefore becomes `2 / n`.
The subsequent endpoints construct the H¹ pair internally: ordinary weak entry
derivatives enter the smooth graph closure through positive-density approximation.
For finite overlap energy, the continuous spectral extension across collisions
supplies those weak equations by the coordinate-line removability argument.
This distinction separates the initial H¹ interface from the completed
finite-overlap interface at the end of the module.
-/

@[expose] public section
open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- The paper's matrix H¹ hypothesis yields the overlap variance bound directly
from the actual Gaussian matrix Poincaré inequality. -/
theorem matrixSpectralLift_H1_gaussian_poincare {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (p : MatrixGaussianSobolevPair n) (hp : p ∈ matrixGaussianH1Completion n)
    (hv : (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F)
    (hd : ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1)))) :
    smoothGinibreVariance n F ≤
      (2/(n : ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hgaussianPoincare := matrixGaussianH1Completion_poincare n hn p hp
  have hvarianceTransport : matrixGaussianL2Variance n p.1 = smoothGinibreVariance n F := by
    rw [matrixGaussianL2Variance_integral]
    have hv2 : (fun A => p.1 A^2) =ᵐ[matrixGaussianMeasure n]
        (fun A => matrixSymmetricLift n F A^2) := hv.mono fun _ h => congrArg (fun v : ℝ => v^2) h
    rw [integral_congr_ae hv, integral_congr_ae hv2]
    change (∫ A, F (matrixMeasurableEigenvalues n A)^2 ∂matrixGaussianMeasure n) -
      (∫ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n)^2 = _
    rw [matrixSpectralLift_integral hn F hF.continuous.measurable hsym,
      matrixSpectralLift_square_integral hn F hF.continuous.measurable hsym]
    let := ginibreMeasure_isProbabilityMeasure hn
    have hFL : MemLp F 2 (ginibreMeasure n) :=
      (matrixSpectralLift_memLp_two_iff hn F hF.continuous.measurable hsym).mp
        ((Lp.memLp p.1).ae_eq hv)
    have hi := hFL.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    unfold smoothGinibreVariance smoothGinibreMean
    rw [show (fun z => (F z-(∫ x, F x ∂ginibreMeasure n))^2) =
      (fun z => F z^2 - 2*(∫ x, F x ∂ginibreMeasure n)*F z +
        (∫ x, F x ∂ginibreMeasure n)^2) by funext z; ring]
    rw [integral_add (f := fun z => F z^2 - 2*(∫ x, F x ∂ginibreMeasure n)*F z)
      (g := fun _ => (∫ x, F x ∂ginibreMeasure n)^2)
      (hFL.integrable_sq.sub (hi.const_mul _)) (integrable_const _),
      integral_sub hFL.integrable_sq (hi.const_mul _), integral_const_mul, integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring
  rw [hvarianceTransport, matrixSpectralLift_H1_energy F hF hsym p hd] at hgaussianPoincare
  convert hgaussianPoincare using 1; ring

/-- An actual ordinary weak pair for a spectral lift gives the matrix Gaussian
route, with graph membership derived from the ordinary derivative equations. -/
theorem matrixSpectralLift_ordinary_weak_gaussian_poincare {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : Configuration n → ℝ) (hF : Differentiable ℝ F)
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
    smoothGinibreVariance n F ≤
      (2/(n : ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let q : MatrixGaussianSobolevPair n := (matrixEntryL2ToMatrix hn e u,
    fun i => matrixEntryL2ToMatrix hn e
      ((configurationGradientComponent m ((matrixEntryRealIndexEquiv e).symm i)).compLpL
        2 (matrixEntryGaussianMeasure e) g))
  have hpairInCompletion : q ∈ matrixGaussianH1Completion n :=
    matrixEntry_full_weak_pair_mem_H1Completion hn e u g hweak
  have hpres :=
    (matrixComplexEntryEquiv_gaussian_preserving hn e).symm (matrixEntryMeasurableEquiv e)
  have hv : (q.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F := by
    filter_upwards [matrixEntryL2ToMatrix_ae hn e u, hpres.quasiMeasurePreserving.ae hu]
      with A hA hB
    change u ((matrixComplexEntryEquiv e).symm A) =
      matrixSymmetricLift n F (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A)) at hB
    exact hA.trans (hB.trans
      (congrArg (matrixSymmetricLift n F) ((matrixComplexEntryEquiv e).apply_symm_apply A)))
  have hd : ∀ i, (q.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A
        (matrixRealCoordinates n (Pi.single i 1))) := by
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
    have h1 := (matrixComplexEntryEquiv e).apply_symm_apply A
    have h2 : matrixEntryRealIndexEquiv e j = i := Equiv.apply_symm_apply _ i
    rw [h1, h2]
  exact matrixSpectralLift_H1_gaussian_poincare hn F hF hsym q hpairInCompletion hv hd

/-- Finite actual overlap energy supplies the original matrix H¹ domain. -/
theorem matrixSpectralLift_finite_overlap_gaussian_poincare_of_entries {n d : ℕ} (hn : 0 < n)
    (e : Fin (d + 1) ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    smoothGinibreVariance n F ≤
      (2/(n : ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
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
  have hfullLift_ae : matrixEntryFullSpectralLift e F =ᵐ[matrixEntryGaussianMeasure e] V := by
    filter_upwards [(matrixComplexEntryEquiv_gaussian_preserving hn e).quasiMeasurePreserving.ae
      (matrixFullSymmetricSpectralLift_eq_ae n F hsym)] with x hx
    exact hx
  have hvalue_fullLift := hu.trans hfullLift_ae.symm
  have hvalue_volume : (u : Configuration (d+1) → ℝ) =ᵐ[volume] matrixEntryFullSpectralLift e F :=
    (matrixEntryGaussian_ae_iff_volume hn e _).mp hvalue_fullLift
  have hweak : ∀ i : Fin (d+1) × Fin 2, ∀ θ : Configuration (d+1) → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i)) := by
    intro i θ hθ hc
    have hgScalar : (fun x => g x i) =ᵐ[matrixEntryGaussianMeasure e]
        (fun x => matrixEntryIntrinsicSpectralGradient e F x i) := by
      filter_upwards [hg] with x hx
      exact congrArg (fun v : EuclideanSpace ℝ (Fin (d+1) × Fin 2) => v i) hx
    have hder := matrixEntryFullSpectralLift_derivative_ae hn e F hF hsym i
    have hgradient_volume : (fun x => g x i) =ᵐ[volume]
        (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i)) :=
      (matrixEntryGaussian_ae_iff_volume hn e _).mp (hgScalar.trans hder.symm)
    have ht := matrixFullSpectralLift_coordinate_weak_test n d e F hF hsym i
      (matrixEntryFullSpectralLift_derivative_locallyIntegrable hn e F hF hsym hE i) θ hθ hc
    calc
      _ = ∫ x, fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i) * θ x :=
          by
        apply integral_congr_ae
        filter_upwards [hgradient_volume] with x hx
        exact congrArg (fun v : ℝ => v * θ x) hx
      _ = -(∫ x, matrixEntryFullSpectralLift e F x * fderiv ℝ θ x (ginibreCoordinateDirection i)) :=
          ht
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hvalue_volume] with x hx
        exact congrArg (fun v : ℝ => v * fderiv ℝ θ x (ginibreCoordinateDirection i)) hx.symm
  exact matrixSpectralLift_ordinary_weak_gaussian_poincare hn e F hF hsym u g hu hg hweak

/-- Concrete full finite-overlap Theorem 1.13 variance endpoint by the Gaussian matrix route. -/
theorem matrixSpectralLift_finite_overlap_gaussian_poincare {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    smoothGinibreVariance n F ≤
      (2/(n : ℝ))*∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let d := n*n-1
  have hm : 1 ≤ n*n := Nat.succ_le_of_lt (Nat.mul_pos hn hn)
  let e : Fin (d+1) ≃ Fin n × Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_prod]
    exact Nat.sub_add_cancel hm)
  exact matrixSpectralLift_finite_overlap_gaussian_poincare_of_entries hn e F hF hsym hFL2 hE

end
end GinibrePoincare
