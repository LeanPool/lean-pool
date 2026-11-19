/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSpectralNumberPolynomial.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaDifferential

/-!
# Alternative spectral number polynomial

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `spectralAdjoint_finiteHermite_memLp`, `finiteGaussianNumberL2_norm_sq`,
`finiteGaussianNumber_memLp`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators ComplexConjugate

/-- Collision-safe finite Hermite raising coefficients. -/
def spectralRaisingCoefficients (n : ℕ) (j : Fin n) :
    (HermiteMultiIndex n →₀ ℂ) →ₗ[ℂ] (HermiteMultiIndex n →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun pq =>
    (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) • Finsupp.single (raiseHermiteIndex j pq) 1)

/-- The literal Gaussian adjoint on a normalized tensor is creation. -/
theorem spectralAdjoint_hermite_ae (n : ℕ) (hn : 0 < n)
    (j : Fin n) (pq : HermiteMultiIndex n) :
    gaussianDbarAdjointTest j (multivariateNormalized n hn pq.1 pq.2) =ᵐ[complexGaussianMeasure n]
      fun z => (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        multivariateNormalized n hn (raiseHermiteIndex j pq).1 (raiseHermiteIndex j pq).2 z := by
  filter_upwards [gaussianHermite_adjoint_creation_ae n hn j pq] with z hz
  have hc := congrArg conj hz
  unfold gaussianDbarAdjointTest
  simpa only [map_sub, map_mul, Complex.conj_natCast, starRingEnd_self_apply,
    Complex.conj_ofReal] using hc

private theorem spectralPartial_const_mul {n : ℕ} (a : ℂ)
    (f : Configuration n → ℂ) (hf : Differentiable ℝ f) (j : Fin n) (z : Configuration n) :
    bkPartial (fun w => a * f w) j z = a * bkPartial f j z := by
  unfold bkPartial bkDirectional
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

private theorem spectralPartial_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Configuration n → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin n) (z : Configuration n) :
    bkPartial (fun w => ∑ i ∈ s, f i w) j z = ∑ i ∈ s, bkPartial (f i) j z := by
  unfold bkPartial bkDirectional
  rw [fderiv_fun_sum (fun i hi => hf i hi z)]
  simp only [sum_apply]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

theorem spectralAdjoint_const_mul {n : ℕ} (a : ℂ)
    (f : Configuration n → ℂ) (hf : Differentiable ℝ f) (j : Fin n) (z : Configuration n) :
    gaussianDbarAdjointTest j (fun w => a * f w) z = a * gaussianDbarAdjointTest j f z := by
  rw [bkAdjoint_eq (hf.const_mul a), bkAdjoint_eq hf]
  dsimp only []
  rw [spectralPartial_const_mul a f hf]
  ring

theorem spectralAdjoint_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Configuration n → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin n) (z : Configuration n) :
    gaussianDbarAdjointTest j (fun w => ∑ i ∈ s, f i w) z =
      ∑ i ∈ s, gaussianDbarAdjointTest j (f i) z := by
  rw [bkAdjoint_eq (Differentiable.fun_sum hf)]
  dsimp only []
  rw [spectralPartial_finset_sum s f hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [bkAdjoint_eq (hf i hi)]

/-- The adjoint is an actual finite Hermite polynomial with raised coefficients. -/
theorem spectralAdjoint_finiteHermite_ae (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    gaussianDbarAdjointTest j (finiteHermiteFunction n hn c) =ᵐ[complexGaussianMeasure n]
      finiteHermiteFunction n hn (spectralRaisingCoefficients n j c) := by
  let H : HermiteMultiIndex n → Configuration n → ℂ :=
    fun pq => multivariateNormalized n hn pq.1 pq.2
  have hd (pq : HermiteMultiIndex n) : Differentiable ℝ (H pq) :=
    (contDiff_multivariateNormalized_real n hn pq.1 pq.2).differentiable (by norm_num)
  have hre : finiteHermiteFunction n hn (spectralRaisingCoefficients n j c) =
      fun z => ∑ pq ∈ c.support, c pq *
        ((Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) * H (raiseHermiteIndex j pq) z) := by
    unfold spectralRaisingCoefficients finiteHermiteFunction
    rw [Finsupp.apply_linearCombination]
    simp only [Function.comp_apply, map_smul, 
      Finsupp.linearCombination_apply, Finsupp.sum]
    funext z
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, H]
  rw [hre]
  have hc : finiteHermiteFunction n hn c = fun z => ∑ pq ∈ c.support, c pq * H pq z := by
    unfold finiteHermiteFunction
    funext z
    simp [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, H]
  rw [hc]
  have hraise : ∀ᵐ z ∂complexGaussianMeasure n, ∀ pq,
      gaussianDbarAdjointTest j (H pq) z =
        (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) * H (raiseHermiteIndex j pq) z :=
    ae_all_iff.mpr (spectralAdjoint_hermite_ae n hn j)
  filter_upwards [hraise] with z hz
  rw [spectralAdjoint_finset_sum _ _ (fun pq _ => (hd pq).const_mul _)]
  simp_rw [spectralAdjoint_const_mul _ _ (hd _) j z, hz]

/-- Genuine L² integrability of the ordinary adjoint of every finite Hermite polynomial. -/
theorem spectralAdjoint_finiteHermite_memLp (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    MemLp (gaussianDbarAdjointTest j (finiteHermiteFunction n hn c)) 2 (complexGaussianMeasure n) :=
        by
  have h := Lp.memLp (finiteHermiteCombination n hn (spectralRaisingCoefficients n j c))
  exact (memLp_congr_ae ((finiteHermiteCombination_coeFn n hn _).trans
    (spectralAdjoint_finiteHermite_ae n hn c j).symm)).mp h

/-- Literal adjoint representative of the concrete raised Gaussian L² polynomial. -/
theorem spectralAdjoint_finiteHermiteCombination_ae (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    (finiteHermiteCombination n hn (spectralRaisingCoefficients n j c) : Configuration n → ℂ)
        =ᵐ[complexGaussianMeasure n]
      gaussianDbarAdjointTest j (finiteHermiteFunction n hn c) :=
  (finiteHermiteCombination_coeFn n hn _).trans (spectralAdjoint_finiteHermite_ae n hn c j).symm

/-- The coefficient lowering operator as a complex-linear map. -/
def spectralLoweringCoefficients (n : ℕ) (j : Fin n) :
    (HermiteMultiIndex n →₀ ℂ) →ₗ[ℂ] (HermiteMultiIndex n →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun pq =>
    (Real.sqrt (n * pq.2 j : ℕ) : ℂ) • Finsupp.single (lowerHermiteIndex j pq) 1)

theorem spectralLoweringCoefficients_eq (n : ℕ) (j : Fin n)
    (c : HermiteMultiIndex n →₀ ℂ) : spectralLoweringCoefficients n j c = loweredCoefficients n c j
        := by
  simp [spectralLoweringCoefficients, Finsupp.linearCombination_apply, loweredCoefficients,
    Finsupp.smul_single, smul_eq_mul, mul_comm]

/-- Diagonal multiplication on finitely supported coefficients. -/
def spectralDiagonalCoefficients {n : ℕ} (w : HermiteMultiIndex n → ℂ) :
    (HermiteMultiIndex n →₀ ℂ) →ₗ[ℂ] (HermiteMultiIndex n →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun pq => w pq • Finsupp.single pq 1)

@[simp] theorem spectralDiagonalCoefficients_apply {n : ℕ} (w : HermiteMultiIndex n → ℂ)
    (c : HermiteMultiIndex n →₀ ℂ) (pq : HermiteMultiIndex n) :
    spectralDiagonalCoefficients w c pq = w pq * c pq := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [map_add, ha, hb, mul_add]
  | single r a =>
    simp [spectralDiagonalCoefficients, Finsupp.linearCombination_single,
      Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_comm]
    split_ifs with h
    · subst r; rfl
    · rfl

/-- Raising after lowering is the exact coordinate number multiplier. -/
theorem spectralRaising_lowering (n : ℕ) (j : Fin n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    spectralRaisingCoefficients n j (spectralLoweringCoefficients n j c) =
      spectralDiagonalCoefficients (fun pq => (n * pq.2 j : ℕ)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single pq a =>
    simp only [spectralRaisingCoefficients, spectralLoweringCoefficients,
      spectralDiagonalCoefficients, Finsupp.linearCombination_single, map_smul]
    by_cases hq : pq.2 j = 0
    · simp [hq]
    · have hpos : 0 < pq.2 j := Nat.pos_of_ne_zero hq
      have hl : (lowerHermiteIndex j pq).2 j + 1 = pq.2 j := by
        simp [lowerHermiteIndex, lowerAt]
        omega
      rw [hl, raiseHermiteIndex_lowerHermiteIndex j pq hpos]
      simp only [smul_smul]
      have hr : (Real.sqrt (n * pq.2 j : ℕ) : ℂ)^2 = (n * pq.2 j : ℕ) := by
        norm_cast
        exact Real.sq_sqrt (Nat.cast_nonneg _)
      congr 1
      simpa only [one_mul, pow_two] using congrArg (fun x : ℂ => a * x) hr

/-- Exact Gaussian number coefficients with eigenvalues `n |q|`. -/
def spectralNumberCoefficients (n : ℕ) :
    (HermiteMultiIndex n →₀ ℂ) →ₗ[ℂ] (HermiteMultiIndex n →₀ ℂ) :=
  spectralDiagonalCoefficients (fun pq => (n * totalAntiDegree pq : ℕ))

/-- The Gaussian `L²` synthesis of the finite Hermite coefficients `c` multiplied by the
number-operator eigenvalues `n |q|`. -/
def finiteGaussianNumberL2 (n : ℕ) (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  finiteHermiteCombination n hn (spectralNumberCoefficients n c)

theorem spectralNumberCoefficients_eq_sum (n : ℕ) (c : HermiteMultiIndex n →₀ ℂ) :
    spectralNumberCoefficients n c =
      ∑ j : Fin n, spectralRaisingCoefficients n j (loweredCoefficients n c j) := by
  simp_rw [← spectralLoweringCoefficients_eq, spectralRaising_lowering]
  ext pq
  simp only [spectralNumberCoefficients, spectralDiagonalCoefficients_apply,
    Finsupp.finsetSum_apply, Nat.cast_mul, totalAntiDegree, Nat.cast_sum]
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Actual differential Gaussian number operator on every finite Hermite polynomial. -/
theorem finiteGaussianNumberL2_ae (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (finiteGaussianNumberL2 n hn c : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
      fun z => ∑ j : Fin n, gaussianDbarAdjointTest j (dbarComponent (finiteHermiteFunction n hn c)
          j) z := by
  unfold finiteGaussianNumberL2
  rw [spectralNumberCoefficients_eq_sum]
  have hlin : finiteHermiteCombination n hn
      (∑ j : Fin n, spectralRaisingCoefficients n j (loweredCoefficients n c j)) =
      ∑ j : Fin n, finiteHermiteCombination n hn
        (spectralRaisingCoefficients n j (loweredCoefficients n c j)) := by
    unfold finiteHermiteCombination
    exact map_sum _ _ _
  rw [hlin]
  have hall : ∀ᵐ z ∂complexGaussianMeasure n, ∀ j,
      (finiteHermiteCombination n hn (spectralRaisingCoefficients n j (loweredCoefficients n c j)) :
        Configuration n → ℂ) z =
        gaussianDbarAdjointTest j (finiteHermiteFunction n hn (loweredCoefficients n c j)) z :=
    ae_all_iff.mpr (fun j => spectralAdjoint_finiteHermiteCombination_ae n hn _ j)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j =>
    finiteHermiteCombination n hn (spectralRaisingCoefficients n j (loweredCoefficients n c j))),
        hall]
    with z hs hall
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hall j]
  congr 1
  funext w
  exact (dbarComponent_finiteHermiteFunction n hn c j w).symm

/-- The spectral number polynomial has precisely the squared multiplier norm. -/
theorem finiteGaussianNumberL2_norm_sq (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    ‖finiteGaussianNumberL2 n hn c‖ ^ 2 =
      c.sum (fun pq a => ((n * totalAntiDegree pq : ℕ) : ℝ)^2 * Complex.normSq a) := by
  let d := spectralNumberCoefficients n c
  have hd (pq : HermiteMultiIndex n) : d pq = (n * totalAntiDegree pq : ℕ) * c pq := by
    simp [d, spectralNumberCoefficients]
  have hsub : d.support ⊆ c.support := by
    intro pq hpq
    rw [Finsupp.mem_support_iff] at hpq ⊢
    intro hc
    apply hpq
    rw [hd, hc, mul_zero]
  unfold finiteGaussianNumberL2
  rw [norm_sq_finiteHermiteCombination]
  change d.sum (fun _ a => Complex.normSq a) = _
  unfold Finsupp.sum
  calc
    (∑ pq ∈ d.support, Complex.normSq (d pq)) =
        ∑ pq ∈ c.support, Complex.normSq (d pq) := by
      apply Finset.sum_subset hsub
      intro pq hpq hnot
      rw [Finsupp.notMem_support_iff.mp hnot]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pq hpq
      rw [hd, Complex.normSq_mul]
      congr 1
      simp [Complex.normSq_apply, pow_two]

/-- Genuine finite-energy domain of the ordinary differential number polynomial. -/
theorem finiteGaussianNumber_memLp (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    MemLp (fun z => ∑ j : Fin n,
      gaussianDbarAdjointTest j (dbarComponent (finiteHermiteFunction n hn c) j) z)
      2 (complexGaussianMeasure n) :=
  (memLp_congr_ae (finiteGaussianNumberL2_ae n hn c)).mp (Lp.memLp (finiteGaussianNumberL2 n hn c))

end
end GinibrePoincare

