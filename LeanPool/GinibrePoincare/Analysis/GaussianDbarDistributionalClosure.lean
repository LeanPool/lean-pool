/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarDistributionalClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarParseval
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianProductIntegral
public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeDivision
public import LeanPool.GinibrePoincare.Analysis.PolynomialCompactApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # Closed Gaussian weak antiholomorphic derivative graph

The weak relation uses the actual Gaussian formal adjoint against compact C¹
test functions. It is an integration-by-parts relation, independently of the
Hermite coefficient representation. Identification with unweighted volume
distributions is a separate step.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The Gaussian formal adjoint of `dbar_j` applied to a test function:
`n · conj (z j) · φ z - conj (dbar_j (conj ∘ φ) z)`. -/
def gaussianDbarAdjointTest {n : ℕ} (j : Fin n)
    (φ : Configuration n → ℂ) (z : Configuration n) : ℂ :=
  (n : ℂ) * conj (z j) * φ z -
    conj (dbarComponent (fun w => conj (φ w)) j z)

theorem gaussianDbarAdjointTest_memLp {n : ℕ} (j : Fin n)
    (φ : Configuration n → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    MemLp (gaussianDbarAdjointTest j φ) 2 (complexGaussianMeasure n) := by
  have hconj : ContDiff ℝ 1 (fun w => conj (φ w)) :=
    Complex.conjCLE.contDiff.comp hφ
  have hcconj : HasCompactSupport (fun w => conj (φ w)) := hc.comp_left (by simp)
  have hcont : Continuous (gaussianDbarAdjointTest j φ) :=
    ((continuous_const.mul ((continuous_apply j).star)).mul hφ.continuous).sub
      ((continuous_dbarComponent hconj j).star)
  have hcompact : HasCompactSupport (gaussianDbarAdjointTest j φ) :=
    (hc.mul_left).sub ((hasCompactSupport_dbarComponent hcconj j).comp_left (by simp))
  exact hcont.memLp_of_hasCompactSupport hcompact

/-- The adjoint test function `gaussianDbarAdjointTest j φ` of a compactly supported `C¹`
function `φ`, as a vector of Gaussian `L²`. -/
def gaussianDbarAdjointTestL2 {n : ℕ} (j : Fin n)
    (φ : Configuration n → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianDbarAdjointTest_memLp j φ hφ hc).toLp (gaussianDbarAdjointTest j φ)

/-- The genuine weighted weak derivative relation against compact smooth tests. -/
def IsGaussianWeakDbar (n : ℕ) (u D : Lp ℂ 2 (complexGaussianMeasure n))
    (j : Fin n) : Prop :=
  ∀ (φ : Configuration n → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ),
    inner ℂ (smoothCompactL2 φ hφ hc) D =
      inner ℂ (gaussianDbarAdjointTestL2 j φ hφ hc) u

theorem isClosed_gaussianWeakDbar_graph (n : ℕ) (j : Fin n) :
    IsClosed {p : Lp ℂ 2 (complexGaussianMeasure n) ×
      Lp ℂ 2 (complexGaussianMeasure n) | IsGaussianWeakDbar n p.1 p.2 j} := by
  simp only [IsGaussianWeakDbar, Set.ofPred_forall]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro hφ
  apply isClosed_iInter
  intro hc
  exact isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner continuous_fst)

theorem gaussianWeakDbar_of_tendsto {n : ℕ} {ι : Type*} {l : Filter ι} [NeBot l] (j : Fin n)
    (p : ι → Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))
    (u D : Lp ℂ 2 (complexGaussianMeasure n))
    (hp : ∀ m, IsGaussianWeakDbar n (p m).1 (p m).2 j)
    (ht : Tendsto p l (𝓝 (u, D))) : IsGaussianWeakDbar n u D j :=
  (isClosed_gaussianWeakDbar_graph n j).mem_of_tendsto ht
    (Eventually.of_forall hp)

/-- Every actual smooth Gaussian L² value/derivative pair satisfies the weak
adjoint identity; compact support of the value is not required. -/
theorem gaussian_smooth_weak_dbar {n : ℕ} (hn : 0 < n) (j : Fin n)
    (u D : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : ContDiff ℝ 1 f)
    (hu : (u : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] f)
    (hD : (D : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] dbarComponent f j) :
    IsGaussianWeakDbar n u D j := by
  intro φ hφ hc
  have hconj : ContDiff ℝ 1 (fun w => conj (φ w)) :=
    Complex.conjCLE.contDiff.comp hφ
  have hcconj : HasCompactSupport (fun w => conj (φ w)) := hc.comp_left (by simp)
  have hA : Integrable (fun z => f z * dbarComponent (fun w => conj (φ w)) j z)
      (complexGaussianMeasure n) :=
    (hf.continuous.mul (continuous_dbarComponent hconj j)).integrable_of_hasCompactSupport
      (hasCompactSupport_dbarComponent hcconj j).mul_left
  have hB : Integrable (fun z => conj (φ z) * dbarComponent f j z)
      (complexGaussianMeasure n) :=
    (hconj.continuous.mul (continuous_dbarComponent hf j)).integrable_of_hasCompactSupport
      hcconj.mul_right
  have hC : Integrable (fun z => (n : ℂ) * z j * f z * conj (φ z))
      (complexGaussianMeasure n) :=
    (((continuous_const.mul (continuous_apply j)).mul hf.continuous).mul
      hconj.continuous).integrable_of_hasCompactSupport hcconj.mul_left
  have hibp := configurationGaussianDbarIntegrationByParts hn j
    (hf.mul hconj) hcconj.mul_left
  have hleft : (∫ z, dbarComponent (fun w => f w * conj (φ w)) j z
      ∂complexGaussianMeasure n) =
      (∫ z, f z * dbarComponent (fun w => conj (φ w)) j z ∂complexGaussianMeasure n) +
      ∫ z, conj (φ z) * dbarComponent f j z ∂complexGaussianMeasure n := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    filter_upwards with z
    rw [dbarComponent_mul (hf.differentiable (by norm_num))
      (hconj.differentiable (by norm_num))]
    ring
  rw [hleft, ← integral_const_mul] at hibp
  have hright : (∫ z, (n : ℂ) * (z j * (f z * conj (φ z)))
      ∂complexGaussianMeasure n) =
      ∫ z, (n : ℂ) * z j * f z * conj (φ z) ∂complexGaussianMeasure n := by
    apply integral_congr_ae
    filter_upwards with z
    ring
  rw [hright] at hibp
  have htest := smoothCompactL2_coeFn φ hφ hc
  have hadj := (gaussianDbarAdjointTest_memLp j φ hφ hc).coeFn_toLp
  have hLi : inner ℂ (smoothCompactL2 φ hφ hc) D =
      ∫ z, conj (φ z) * dbarComponent f j z ∂complexGaussianMeasure n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [htest, hD] with z hz hDz
    rw [RCLike.inner_apply, hz, hDz]
    ring
  have hRi : inner ℂ (gaussianDbarAdjointTestL2 j φ hφ hc) u =
      ∫ z, ((n : ℂ) * z j * f z * conj (φ z) -
        f z * dbarComponent (fun w => conj (φ w)) j z) ∂complexGaussianMeasure n := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hadj, hu] with z hz huz
    change (gaussianDbarAdjointTestL2 j φ hφ hc : Configuration n → ℂ) z =
      gaussianDbarAdjointTest j φ z at hz
    rw [RCLike.inner_apply, hz, huz]
    simp only [gaussianDbarAdjointTest, map_sub, map_mul, Complex.conj_natCast,
      starRingEnd_self_apply]
    ring
  rw [hLi, hRi]
  rw [integral_sub hC hA]
  linear_combination hibp

theorem contDiff_finiteHermiteFunction (n : ℕ) (hn : 0 < n)
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ) :
    ContDiff ℝ 1 (ComplexHermite.finiteHermiteFunction n hn c) := by
  classical
  unfold ComplexHermite.finiteHermiteFunction
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [show (∑ pq ∈ c.support,
    c pq • ComplexHermite.multivariateNormalized n hn pq.1 pq.2) =
      (fun z => ∑ pq ∈ c.support,
        c pq • ComplexHermite.multivariateNormalized n hn pq.1 pq.2 z) by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply]]
  exact ContDiff.sum fun pq _ =>
    (contDiff_multivariateNormalized_real n hn pq.1 pq.2).const_smul (c pq)

/-- Finite Hermite lowering belongs to the independently defined weak test graph. -/
theorem gaussian_finiteHermite_weak_dbar (n : ℕ) (hn : 0 < n)
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    IsGaussianWeakDbar n (ComplexHermite.finiteHermiteCombination n hn c)
      (finiteDbarComponentL2 n hn c j) j :=
  gaussian_smooth_weak_dbar hn j _ _ _ (contDiff_finiteHermiteFunction n hn c)
    (ComplexHermite.finiteHermiteCombination_coeFn n hn c)
    (finiteDbarComponentL2_coeFn n hn c j)

end
end GinibrePoincare

