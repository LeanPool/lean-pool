/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianEntireHilbertIdentification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSeriesBounds
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-! # Linking the Hilbert expansion to a pointwise entire series

Hilbert-space convergence alone does not give pointwise convergence. The first
lemma bridges the two: convergence in L² gives a subsequence converging almost
everywhere, while pointwise summability identifies its limit. Countability lets
all finite-sum representative identities hold on one common set of full measure.

For the zero Hermite mode, summing over the antiholomorphic index leaves only
index zero. The norm bound on each Hilbert coefficient then invokes the factorial
series estimates of `GaussianEntireSeriesBounds` to prove pointwise summability.
The resulting series represents the orthogonal projection almost everywhere;
entire regularity is supplied separately by `GaussianEntireDifferentiability`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

/-- A countable Hilbert-space series agreeing with a pointwise summable
series has that pointwise sum as an almost-everywhere representative. Absolute
summability of the Hilbert-space norms is not required. -/
theorem lp_hasSum_pointwise_representative {ι : Type*} [Countable ι]
    {n : ℕ} (F : ι → Lp ℂ 2 (complexGaussianMeasure n))
    (f : ι → Configuration n → ℂ) (u : Lp ℂ 2 (complexGaussianMeasure n))
    (hF : HasSum F u) (hrep : ∀ i, F i =ᵐ[complexGaussianMeasure n] f i)
    (hf : ∀ z, Summable (fun i => f i z)) :
    (fun z => ∑' i, f i z) =ᵐ[complexGaussianMeasure n] u := by
  have hs : ∀ᵐ z ∂complexGaussianMeasure n, ∀ s : Finset ι,
      (∑ i ∈ s, F i) z = ∑ i ∈ s, f i z := by
    rw [ae_all_iff]
    intro s
    have hreps : ∀ᵐ z ∂complexGaussianMeasure n, ∀ i, F i z = f i z :=
      ae_all_iff.mpr hrep
    filter_upwards [Lp.coeFn_fun_finsetSum s F, hreps] with z hz hz'
    rw [hz]
    exact Finset.sum_congr rfl (fun i _ => hz' i)
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae'
  filter_upwards [hs, hlim] with z hz hzlim
  have hpoint := (hf z).hasSum.comp hns
  apply tendsto_nhds_unique hpoint
  convert hzlim using 1
  funext k
  exact (hz (ns k)).symm

open ComplexHermite

/-- Collapse the full Hilbert reconstruction of the degree-zero projection
into its genuine holomorphic multi-index series. -/
theorem hasSum_gaussianZeroMode_holomorphicBasis {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    HasSum (fun p : Fin n → ℕ => gaussianHermiteCoefficient hn u (p, 0) •
      multivariateNormalizedL2 n hn p 0) (gaussianHermiteMode hn 0 u) := by
  classical
  have hs := (gaussianHermiteHilbertBasis n hn).hasSum_repr (gaussianHermiteMode hn 0 u)
  change HasSum (fun pq => gaussianHermiteCoefficient hn (gaussianHermiteMode hn 0 u) pq •
    (gaussianHermiteHilbertBasis n hn) pq) _ at hs
  simp only [gaussianHermiteHilbertBasis_apply] at hs
  apply hs.prod_fiberwise
  intro p
  convert hasSum_ite_eq (0 : Fin n → ℕ)
    (gaussianHermiteCoefficient hn u (p, 0) • multivariateNormalizedL2 n hn p 0) using 1
  funext q
  rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode]
  by_cases hq : q = 0
  · subst q
    simp [totalAntiDegree]
  · have ht : totalAntiDegree (p, q) ≠ 0 := by
      intro hz
      have hall : ∀ i : Fin n, q i = 0 := by
        have hh := (Finset.sum_eq_zero_iff).mp hz
        exact fun i => hh i (Finset.mem_univ i)
      exact hq (funext hall)
    simp [ht, hq]

theorem gaussianHermiteCoefficient_norm_le {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    ‖gaussianHermiteCoefficient hn u pq‖ ≤ ‖u‖ := by
  calc
    _ ≤ ‖(gaussianHermiteHilbertBasis n hn).repr u‖ :=
      lp.norm_apply_le_norm (by norm_num) _ pq
    _ = ‖u‖ := (gaussianHermiteHilbertBasis n hn).repr.norm_map u

/-- The genuine pointwise holomorphic series represents the Gaussian
zero-mode orthogonal projection almost everywhere. -/
theorem gaussianZeroMode_holomorphic_series_ae {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (fun z => ∑' p : Fin n → ℕ, gaussianHermiteCoefficient hn u (p, 0) *
      multivariateNormalized n hn p 0 z) =ᵐ[complexGaussianMeasure n]
        gaussianHermiteMode hn 0 u := by
  apply lp_hasSum_pointwise_representative _ _ _ (hasSum_gaussianZeroMode_holomorphicBasis hn u)
  · intro p
    filter_upwards [Lp.coeFn_smul (gaussianHermiteCoefficient hn u (p, 0))
      (multivariateNormalizedL2 n hn p 0), multivariateNormalizedL2_coeFn n hn p 0] with z hs hz
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul, hz]
  · exact summable_holomorphicHermite_series n hn _
      (fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0))

end
end GinibrePoincare

