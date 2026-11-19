/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarEqualitySpace.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarWeakEquality
public import LeanPool.GinibrePoincare.Analysis.WeightedSeriesTruncation

/-! # The degree-zero plus degree-one Gaussian equality space
This is the direct sum of the two actual closed Hermite subspaces.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- The sum of the closed Hermite spans of total antiholomorphic degree `0` and `1` in
Gaussian `L²`. -/
def gaussianGapEqualitySpace (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
  hermiteAntiDegreeClosedSpan n hn 0 ⊔ hermiteAntiDegreeClosedSpan n hn 1

theorem gaussianHermiteMode_zero_of_mem_other {n : ℕ} (hn : 0 < n)
    {d e : ℕ} (hde : d ≠ e) (u : Lp ℂ 2 (complexGaussianMeasure n))
    (hu : u ∈ hermiteAntiDegreeClosedSpan n hn e) : gaussianHermiteMode hn d u = 0 := by
  have he : gaussianHermiteMode hn e u = u := by
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hu
  rw [← he]
  exact gaussianHermiteMode_cross_eq_zero hn hde u

theorem gaussianHermiteModes_ge_two_zero_iff_reconstruction {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∀ d : ℕ, 2 ≤ d → gaussianHermiteMode hn d u = 0) ↔
      u = gaussianHermiteMode hn 0 u + gaussianHermiteMode hn 1 u := by
  constructor
  · intro hu
    calc
      u = ∑' d, gaussianHermiteMode hn d u := (tsum_gaussianHermiteMode hn u).symm
      _ = ∑ d ∈ Finset.range 2, gaussianHermiteMode hn d u :=
        tsum_eq_sum (fun d hd => hu d (by simpa only [Finset.mem_range, not_lt] using hd))
      _ = _ := by simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  · intro hu d hd
    rw [hu, gaussianHermiteMode_eq_antiDegreeProjection, map_add,
      ← gaussianHermiteMode_eq_antiDegreeProjection, ← gaussianHermiteMode_eq_antiDegreeProjection,
      gaussianHermiteMode_cross_eq_zero hn (by omega),
      gaussianHermiteMode_cross_eq_zero hn (by omega)]
    simp

theorem mem_gaussianGapEqualitySpace_iff {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    u ∈ gaussianGapEqualitySpace n hn ↔
      ∀ d : ℕ, 2 ≤ d → gaussianHermiteMode hn d u = 0 := by
  constructor
  · intro hu d hd
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hu
    rw [← hxy, gaussianHermiteMode_eq_antiDegreeProjection, map_add,
      ← gaussianHermiteMode_eq_antiDegreeProjection, ← gaussianHermiteMode_eq_antiDegreeProjection,
      gaussianHermiteMode_zero_of_mem_other hn (by omega) x hx,
      gaussianHermiteMode_zero_of_mem_other hn (by omega) y hy]
    simp
  · intro hu
    rw [(gaussianHermiteModes_ge_two_zero_iff_reconstruction hn u).mp hu]
    exact Submodule.add_mem_sup (gaussianHermiteMode_mem_closedSpan hn 0 u)
      (gaussianHermiteMode_mem_closedSpan hn 1 u)

theorem disjoint_gaussianGapEquality_summands (n : ℕ) (hn : 0 < n) :
    Disjoint (hermiteAntiDegreeClosedSpan n hn 0 : Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)))
      (hermiteAntiDegreeClosedSpan n hn 1 : Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n))) := by
  apply Submodule.disjoint_def.mpr
  intro u hu₀ hu₁
  have h0 : gaussianHermiteMode hn 0 u = u := by
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hu₀
  exact h0.symm.trans (gaussianHermiteMode_zero_of_mem_other hn (by decide) u hu₁)

theorem isClosed_gaussianGapEqualitySpace (n : ℕ) (hn : 0 < n) :
    IsClosed (gaussianGapEqualitySpace n hn : Set (Lp ℂ 2 (complexGaussianMeasure n))) := by
  have he : (gaussianGapEqualitySpace n hn : Set _) =
      ⋂ d : {d : ℕ // 2 ≤ d}, {u | gaussianHermiteMode hn d u = 0} := by
    ext u
    constructor
    · intro hu
      apply Set.mem_iInter.mpr
      intro d
      exact (mem_gaussianGapEqualitySpace_iff hn u).mp hu d.1 d.2
    · intro hu
      apply (mem_gaussianGapEqualitySpace_iff hn u).mpr
      intro d hd
      exact Set.mem_iInter.mp hu ⟨d, hd⟩
  rw [he]
  apply isClosed_iInter
  intro d
  apply isClosed_eq _ continuous_const
  change Continuous (fun u : Lp ℂ 2 (complexGaussianMeasure n) => gaussianHermiteMode hn d u)
  rw [show (fun u : Lp ℂ 2 (complexGaussianMeasure n) => gaussianHermiteMode hn d u) =
    hermiteAntiDegreeProjection n hn d by funext u; exact
                                            gaussianHermiteMode_eq_antiDegreeProjection hn u d]
  exact (hermiteAntiDegreeProjection n hn d).continuous

/-- The exact equality space on the maximal ordinary Schwartz weak domain. -/
theorem gaussianSchwartzDbar_gap_equality_iff_mem_space {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) :
    (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 =
      ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 ↔
      u ∈ gaussianGapEqualitySpace n hn :=
  (gaussianSchwartzDbar_gap_equality_iff hn u D hu).trans
    (mem_gaussianGapEqualitySpace_iff hn u).symm

/-- Every Hermite degree subspace is represented by its actual square-summable
 coefficient series indexed by that degree. -/
theorem hasSum_gaussianHermiteMode_degreeBasis {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (d : ℕ) :
    HasSum (fun pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d} =>
      gaussianHermiteCoefficient hn u pq.1 •
        multivariateNormalizedL2 n hn pq.1.1 pq.1.2) (gaussianHermiteMode hn d u) := by
  classical
  let T := gaussianHermiteModeTerm hn u d
  let S : Set (HermiteMultiIndex n) := {pq | totalAntiDegree pq = d}
  have hs : Summable (fun pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d} =>
      gaussianHermiteCoefficient hn u pq.1 • multivariateNormalizedL2 n hn pq.1.1 pq.1.2) := by
    have ht := (summable_gaussianHermiteModeTerm hn u d).subtype (fun pq => totalAntiDegree pq = d)
    exact ht.congr (fun pq => by simp [gaussianHermiteModeTerm, pq.2])
  have hi : S.indicator T = T := by
    funext pq
    by_cases h : totalAntiDegree pq = d <;> simp [S, T, gaussianHermiteModeTerm, h]
  have he : (∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = d},
      gaussianHermiteCoefficient hn u pq.1 • multivariateNormalizedL2 n hn pq.1.1 pq.1.2) =
      gaussianHermiteMode hn d u := by
    calc
      _ = ∑' pq : S, T pq := tsum_congr (fun pq => by
        have hp : totalAntiDegree pq.1 = d := pq.2
        simp [T, gaussianHermiteModeTerm, hp])
      _ = ∑' pq, S.indicator T pq := tsum_subtype S T
      _ = _ := by rw [hi]; rfl
  exact he ▸ hs.hasSum

/-- Literal degree-zero plus degree-one convergent Hermite representation
 and its exact square-summable coefficient norm. -/
theorem gaussianGapEqualitySpace_coefficient_expansion {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : u ∈ gaussianGapEqualitySpace n hn) :
    u = (∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = 0},
      gaussianHermiteCoefficient hn u pq.1 • multivariateNormalizedL2 n hn pq.1.1 pq.1.2) +
      ∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = 1},
        gaussianHermiteCoefficient hn u pq.1 • multivariateNormalizedL2 n hn pq.1.1 pq.1.2 ∧
    Summable (fun pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = 0} =>
      ‖gaussianHermiteCoefficient hn u pq.1‖ ^ 2) ∧
    Summable (fun pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = 1} =>
      ‖gaussianHermiteCoefficient hn u pq.1‖ ^ 2) ∧
    (∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = 0},
      ‖gaussianHermiteCoefficient hn u pq.1‖ ^ 2) +
      (∑' pq : {pq : HermiteMultiIndex n // totalAntiDegree pq = 1},
        ‖gaussianHermiteCoefficient hn u pq.1‖ ^ 2) = ‖u‖ ^ 2 := by
  have hz := (mem_gaussianGapEqualitySpace_iff hn u).mp hu
  have hrec := (gaussianHermiteModes_ge_two_zero_iff_reconstruction hn u).mp hz
  have hs0 := hasSum_coefficient_norm_sq_of_totalAntiDegree hn u 0
  have hs1 := hasSum_coefficient_norm_sq_of_totalAntiDegree hn u 1
  refine ⟨?_, hs0.summable, hs1.summable, ?_⟩
  · rw [(hasSum_gaussianHermiteMode_degreeBasis hn u 0).tsum_eq,
      (hasSum_gaussianHermiteMode_degreeBasis hn u 1).tsum_eq]
    exact hrec
  · rw [hs0.tsum_eq, hs1.tsum_eq]
    have hnorm : (∑' d, ‖gaussianHermiteMode hn d u‖ ^ 2) =
        ‖gaussianHermiteMode hn 0 u‖ ^ 2 + ‖gaussianHermiteMode hn 1 u‖ ^ 2 := by
      calc
        _ = ∑ d ∈ Finset.range 2, ‖gaussianHermiteMode hn d u‖ ^ 2 :=
          tsum_eq_sum (fun d hd => by rw [hz d (by simpa only [Finset.mem_range, not_lt] using hd)];
                                        simp)
        _ = _ := by simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact hnorm.symm.trans (tsum_norm_sq_gaussianHermiteMode hn u)

/-- Every member of the equality space lies in the maximal genuine derivative
 domain; the space characterization does not hide a finite-energy hypothesis. -/
theorem gaussianGapEqualitySpace_exists_schwartzDbar {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : u ∈ gaussianGapEqualitySpace n hn) :
    ∃ D : Fin n → Lp ℂ 2 (complexGaussianMeasure n),
      (∀ j, IsGaussianSchwartzDbar n u (D j) j) ∧
      (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 =
        ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 := by
  classical
  have hm := (mem_gaussianGapEqualitySpace_iff hn u).mp hu
  have hc (r : HermiteMultiIndex n) (hr : 2 ≤ totalAntiDegree r) :
      gaussianHermiteCoefficient hn u r = 0 := by
    have hi := inner_basis_gaussianHermiteMode hn u (totalAntiDegree r) r
    rw [hm _ hr, inner_zero_right, ite_eq_left rfl] at hi
    exact hi.symm
  have hex (j : Fin n) : ∃ Dj : Lp ℂ 2 (complexGaussianMeasure n), IsGaussianWeakDbar n u Dj j := by
    apply (gaussianWeakDbar_exists_iff_summable hn u j).mpr
    have hs := (hasSum_norm_sq_gaussianHermiteCoefficient hn u).summable.comp_injective
      (raiseHermiteIndex_injective j)
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs.mul_left (n : ℝ))
    intro pq
    by_cases hd : 2 ≤ totalAntiDegree (raiseHermiteIndex j pq)
    · rw [hc _ hd, mul_zero, norm_zero]
      simp only [zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    · have hj : pq.2 j = 0 := by
        have h := Finset.single_le_sum (fun i _ => Nat.zero_le ((raiseHermiteIndex j pq).2 i))
          (Finset.mem_univ j)
        change Function.update pq.2 j (pq.2 j + 1) j ≤ totalAntiDegree (raiseHermiteIndex j pq) at h
        rw [Function.update_self] at h
        omega
      simp only [hj, zero_add, mul_one, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg n)]
      rfl
  choose D hD using hex
  have hS : ∀ j, IsGaussianSchwartzDbar n u (D j) j :=
    fun j => (gaussianSchwartzDbar_iff_weak hn u (D j) j).mpr (hD j)
  exact ⟨D, hS, (gaussianSchwartzDbar_gap_equality_iff_mem_space hn u D hS).mpr hu⟩

end
end GinibrePoincare

