/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarSmoothTests.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakDomain

/-! # Schwartz test functions and the Gaussian weak graph
Smooth compact tests already detect every Hermite coefficient. Consequently
allowing compact C¹ tests gives the same Gaussian L² derivative graph.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexConjugate BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem contDiff_normalizedEval_real_smooth (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    ContDiff ℝ ∞ (normalizedEval n hn p q) := by
  unfold normalizedEval normalized raw
  simp only [map_mul, map_sum, map_pow, MvPolynomial.eval_C,
    Z, W, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have hsum : ContDiff ℝ ∞ (fun z : ℂ ↦
      ∑ k ∈ Finset.range (min p q + 1),
        ((-((n : ℝ)⁻¹) : ℂ) ^ k) * (k.factorial : ℂ) *
          (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ) *
          z ^ (p - k) * conj z ^ (q - k)) := by
    apply ContDiff.sum
    intro k hk
    exact ((contDiff_const.mul (contDiff_id.pow (p - k))).mul
      ((ContinuousLinearEquiv.contDiff Complex.conjCLE).pow (q - k)))
  exact (show ContDiff ℝ ∞ (fun _ : ℂ ↦
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ)) from
    contDiff_const).mul hsum

theorem contDiff_multivariateNormalized_real_smooth (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    ContDiff ℝ ∞ (multivariateNormalized n hn p q) := by
  unfold multivariateNormalized
  let f : Fin n → Configuration n → ℂ :=
    fun i z ↦ normalizedEval n hn (p i) (q i) (z i)
  have hf : ∀ i, ContDiff ℝ ∞ (f i) := fun i ↦
    (contDiff_normalizedEval_real_smooth n hn (p i) (q i)).comp
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  change ContDiff ℝ ∞ (fun z ↦ ∏ i ∈ Finset.univ, f i z)
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Configuration n ↦ (1 : ℂ)))
  | @insert i t hit ih =>
      simpa only [Finset.prod_insert hit] using (hf i).mul ih

/-- `D` is a weak `∂̄_j` derivative of `u` against smooth compactly supported tests `θ`:
`∫ θ D dγ = ∫ u (n z_j θ - ∂̄_j θ) dγ` for the complex Gaussian measure `γ`. -/
def IsGaussianSmoothTestDbar (n : ℕ)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) : Prop :=
  ∀ (θ : Configuration n → ℂ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
    (∫ z, θ z * D z ∂complexGaussianMeasure n) =
      ∫ z, u z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)
        ∂complexGaussianMeasure n

theorem gaussianSmoothTestDbar_hermiteCoefficient {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianSmoothTestDbar n u D j) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn D pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq) := by
  let H := multivariateNormalized n hn pq.2 pq.1
  have hH : ContDiff ℝ ∞ H := contDiff_multivariateNormalized_real_smooth n hn _ _
  have hi : Integrable (fun z => H z * D z) (complexGaussianMeasure n) :=
    (memLp_two_multivariateNormalized n hn pq.2 pq.1).integrable_mul (Lp.memLp D)
  have hl := integral_gaussianSpatialCutoff_tendsto (fun z => H z * D z) hi
  have hr := gaussianHermiteCutoff_adjointIntegral_tendsto hn u j pq
  have he (m : ℕ) :
      (∫ z, (ginibreSpatialCutoff n m z : ℂ) * (H z * D z) ∂complexGaussianMeasure n) =
      ∫ z, u z * ((n : ℂ) * z j * ((ginibreSpatialCutoff n m z : ℂ) * H z) -
        dbarComponent (fun w => (ginibreSpatialCutoff n m w : ℂ) * H w) j z)
        ∂complexGaussianMeasure n := by
    have ht := hu (fun z => (ginibreSpatialCutoff n m z : ℂ) * H z)
      ((Complex.ofRealCLM.contDiff.comp (ginibreSpatialCutoff_smooth n m)).mul hH)
      (((ginibreSpatialCutoff_compact n m).comp_left Complex.ofReal_zero).mul_right)
    convert ht using 1
    congr 1
    funext z
    ring
  have hlim := tendsto_nhds_unique hl (hr.congr (fun m => (he m).symm))
  rw [← gaussianHermiteCoefficient_eq_integral hn D pq] at hlim
  exact hlim

theorem gaussianSmoothTestDbar_iff_weak {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    IsGaussianSmoothTestDbar n u D j ↔ IsGaussianWeakDbar n u D j := by
  constructor
  · intro h
    exact gaussianWeakDbar_of_hermiteCoefficient hn u D j
      (gaussianSmoothTestDbar_hermiteCoefficient hn u D j h)
  · intro h θ hθ hc
    exact gaussianWeakDbar_integral_identity u D j h θ (hθ.of_le (by simp)) hc

/-- The literal Schwartz distribution relation uses ordinary Lebesgue
integrals and only compact C∞ test functions. -/
def IsGaussianSchwartzDbar (n : ℕ)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) : Prop :=
  LocallyIntegrable u volume ∧ LocallyIntegrable D volume ∧
    ∀ (θ : Configuration n → ℂ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ z, θ z * D z) = -(∫ z, u z * dbarComponent θ j z)

theorem gaussianSchwartzDbar_smoothTest {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianSchwartzDbar n u D j) :
    IsGaussianSmoothTestDbar n u D j := by
  intro θ hθ hc
  let ρ : Configuration n → ℂ := fun z => gaussianLebesgueDensityReal n z
  have hρ : ContDiff ℝ ∞ ρ := Complex.ofRealCLM.contDiff.comp
    (contDiff_gaussianLebesgueDensityReal n)
  have he := hu.2.2 (fun z => ρ z * θ z) (hρ.mul hθ) hc.mul_left
  rw [integral_complexGaussian_eq_density_volume hn,
    integral_complexGaussian_eq_density_volume hn]
  change (∫ z, ρ z * (θ z * D z)) =
    ∫ z, ρ z * (u z * ((n : ℂ) * z j * θ z - dbarComponent θ j z))
  have hd (z : Configuration n) : dbarComponent (fun z => ρ z * θ z) j z =
      -(ρ z * ((n : ℂ) * z j * θ z - dbarComponent θ j z)) := by
    rw [dbarComponent_mul (hρ.differentiable (by norm_num))
      (hθ.differentiable (by norm_num))]
    have hr := dbarComponent_gaussianLebesgueDensityReal n j z
    change dbarComponent ρ j z = -(n : ℂ) * z j * ρ z at hr
    rw [hr]
    ring
  calc
    _ = ∫ z, (ρ z * θ z) * D z := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = _ := he
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with z
      rw [hd]
      ring

/-- No extra regularity hypothesis: the compact C¹ Gaussian weak graph
is exactly the ordinary Schwartz distributional derivative graph on L². -/
theorem gaussianSchwartzDbar_iff_weak {n : ℕ} (hn : 0 < n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    IsGaussianSchwartzDbar n u D j ↔ IsGaussianWeakDbar n u D j := by
  constructor
  · intro h
    exact (gaussianSmoothTestDbar_iff_weak hn u D j).mp
      (gaussianSchwartzDbar_smoothTest hn u D j h)
  · intro h
    have hv := gaussianWeakDbar_volumeDistributional hn u D j h
    exact ⟨hv.1, hv.2.1, fun θ hθ hc => hv.2.2 θ (hθ.of_le (by simp)) hc⟩

end
end GinibrePoincare

