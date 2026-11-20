/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryEqualityAnalytic.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryFirstModeSeries
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarEqualitySpace

/-!
# Correspondence auxiliary equality analytic

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `gaussianGapEqualitySpace_real_analytic_representative`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

private theorem sum_one_index (n : ℕ) (q : Fin n → ℕ) (hq : ∑ i, q i = 1) :
    ∃ j : Fin n, q = raiseAt 0 j := by
  obtain ⟨j, hj, hqj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ i, q i ≠ 0)
  have hjle : q j ≤ 1 := by
    rw [← hq]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  have hjone : q j = 1 := by omega
  refine ⟨j,?_⟩
  have herase : ∑ i ∈ Finset.univ.erase j, q i = 0 := by
    have h := Finset.add_sum_erase Finset.univ q (Finset.mem_univ j)
    omega
  funext i
  by_cases hi : i = j
  · subst i
    simp [raiseAt, hjone]
  · have hqi := (Finset.sum_eq_zero_iff.mp herase) i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    simp [raiseAt, Function.update_of_ne hi, hqi]

private theorem equality_coeff_zero {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : u ∈ gaussianGapEqualitySpace n hn)
    (p q : Fin n → ℕ) (hq : 2 ≤ ∑ i, q i) : gaussianHermiteCoefficient hn u (p, q) = 0 := by
  have hm := (mem_gaussianGapEqualitySpace_iff hn u).mp hu (∑ i, q i) hq
  have hi := inner_basis_gaussianHermiteMode hn u (∑ i, q i) (p, q)
  rw [hm] at hi
  simpa [totalAntiDegree, gaussianHermiteCoefficient_eq_inner] using hi.symm

/-- Every vector in the actual closed Gaussian gap equality space has a
jointly real-analytic representative on the whole configuration space. -/
theorem gaussianGapEqualitySpace_real_analytic_representative {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : u ∈ gaussianGapEqualitySpace n hn) :
    ∃ f : Configuration n → ℂ, (∀ z, AnalyticAt ℝ f z) ∧
      f =ᵐ[complexGaussianMeasure n] u := by
  classical
  let T : HermiteMultiIndex n → Lp ℂ 2 (complexGaussianMeasure n) := fun pq =>
    gaussianHermiteCoefficient hn u pq • multivariateNormalizedL2 n hn pq.1 pq.2
  let G : (Fin n → ℕ) → Configuration n → ℂ := fun q z =>
    ∑' p, gaussianHermiteCoefficient hn u (p, q) * multivariateNormalized n hn p q z
  let v : (Fin n → ℕ) → Lp ℂ 2 (complexGaussianMeasure n) := fun q => ∑' p, T (p, q)
  let S := (finite_holomorphic_degree_fiber n 0).toFinset ∪
    (finite_holomorphic_degree_fiber n 1).toFinset
  have hs : HasSum T u := by
    simpa only [T, gaussianHermiteCoefficient, gaussianHermiteHilbertBasis_apply] using
      (gaussianHermiteHilbertBasis n hn).hasSum_repr u
  have hfixed (q : Fin n → ℕ) : Summable (fun p => T (p, q)) :=
    hs.summable.comp_injective (fun _ _ h => congrArg Prod.fst h)
  have hG (q : Fin n → ℕ) (hq : q ∈ S) :
      (∀ z, AnalyticAt ℝ (G q) z) ∧
      (∀ z, Summable (fun p => gaussianHermiteCoefficient hn u (p, q) *
        multivariateNormalized n hn p q z)) := by
    have hdeg : (∑ i, q i = 0) ∨ (∑ i, q i = 1) := by
      simpa only [S, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hq
    rcases hdeg with hq0 | hq1
    · have hzero : q = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff.mp hq0) i (Finset.mem_univ i)
      subst q
      exact ⟨holomorphicHermite_series_real_analytic n hn _
        (fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0)),
        summable_holomorphicHermite_series n hn _
          (fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0))⟩
    · obtain ⟨j, rfl⟩ := sum_one_index n q hq1
      exact ⟨firstModeHermite_series_real_analytic n hn _
        (fun p => gaussianHermiteCoefficient_norm_le hn u (p, raiseAt 0 j)) j,
        firstModeHermite_series_summable n hn _
          (fun p => gaussianHermiteCoefficient_norm_le hn u (p, raiseAt 0 j)) j⟩
  have hae (q : Fin n → ℕ) (hq : q ∈ S) : G q =ᵐ[complexGaussianMeasure n] v q := by
    apply lp_hasSum_pointwise_representative _ _ _ (hfixed q).hasSum
    · intro p
      filter_upwards [Lp.coeFn_smul (gaussianHermiteCoefficient hn u (p, q))
        (multivariateNormalizedL2 n hn p q), multivariateNormalizedL2_coeFn n hn p q]
        with z h1 h2
      rw [h1]
      simp only [Pi.smul_apply, smul_eq_mul, h2]
    · exact (hG q hq).2
  have hrec : u = ∑ q ∈ S, v q := by
    have hswap : HasSum (fun pq : HermiteMultiIndex n => T pq.swap) u :=
      (Equiv.prodComm _ _).hasSum_iff.mpr hs
    have hsum := hswap.prod_fiberwise (fun q => (hfixed q).hasSum)
    rw [← hsum.tsum_eq]
    apply tsum_eq_sum
    intro q hq
    have hdeg : 2 ≤ ∑ i, q i := by
      have hh : ¬ ((∑ i, q i = 0) ∨ (∑ i, q i = 1)) := by
        simpa only [S, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hq
      omega
    have hterm : ∀ p, T (p, q) = 0 := fun p => by
      simp [T, equality_coeff_zero hn u hu p q hdeg]
    simp only [hterm, tsum_zero]
  refine ⟨fun z => ∑ q ∈ S, G q z,?_,?_⟩
  · intro z
    exact S.analyticAt_fun_sum (fun q hq => (hG q hq).1 z)
  · have hall : ∀ᵐ z ∂complexGaussianMeasure n, ∀ q ∈ S, G q z = v q z := by
      apply ae_all_iff.mpr
      intro q
      by_cases hq : q ∈ S
      · exact (hae q hq).mono (fun z hz _ => hz)
      · exact ae_of_all _ (fun z h => (hq h).elim)
    have hsum := Lp.coeFn_fun_finsetSum S v
    filter_upwards [hall, hsum] with z hz hv
    rw [hrec, hv]
    exact Finset.sum_congr rfl (fun q hq => hz q hq)

end
end GinibrePoincare
