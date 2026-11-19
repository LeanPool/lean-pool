/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianDbarWeakEquality.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianDbarSmoothTests
public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarInfiniteEnergy
public import Mathlib.Analysis.Complex.Liouville
public import LeanPool.GinibrePoincare.Analysis.GaussianEntireReconstruction

/-! # Gaussian antiholomorphic gap on the full weak graph
The gap and equality statements concern arbitrary weighted L² functions with
actual distributional derivatives, rather than smooth core functions.
-/

@[expose] public section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Exact first-order energy series on the independently defined weak domain. -/
theorem gaussianWeakDbar_energy_series {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    HasSum (fun d : ℕ => d * ‖gaussianHermiteMode hn d u‖ ^ 2)
      ((1 / n : ℝ) * ∑ j : Fin n, ‖D j‖ ^ 2) :=
  hasSum_weighted_gaussianHermiteMode_of_coefficient_raise hn u D
    (fun j pq => gaussianWeakDbar_hermiteCoefficient hn u (D j) j (hu j) pq)

/-- The exact sum of squares deficit, without a core approximation hypothesis. -/
theorem gaussianWeakDbar_deficit_sumSquares {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    (∑ j : Fin n, ∑ k : Fin n,
      ‖gaussianInverseSquareRootSecondSynthesisCLM hn j k (D j)‖ ^ 2) =
      n * ((1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 -
        (‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2)) :=
  gaussianInverseSquareRootSecondSynthesis_total_energy hn u D
    (fun j pq => gaussianWeakDbar_hermiteCoefficient hn u (D j) j (hu j) pq)

/-- Exact Gaussian gap deficit as the convergent antiholomorphic mode tail. -/
theorem gaussianWeakDbar_deficit_modeTail {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    Summable (fun k : ℕ => (k : ℝ) * positiveHermiteModeMass hn u k) ∧
      (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 -
        (‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2) =
          modeTail (positiveHermiteModeMass hn u) := by
  have hc := fun j pq => gaussianWeakDbar_hermiteCoefficient hn u (D j) j (hu j) pq
  obtain ⟨ht, he⟩ := gaussianInverseSquareRootSecondSynthesis_total_energy_modeTail hn u D hc
  refine ⟨ht, ?_⟩
  rw [gaussianWeakDbar_deficit_sumSquares hn u D hu] at he
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') he

/-- Sharp Gaussian antiholomorphic Poincaré inequality on the full weak graph. -/
theorem gaussianWeakDbar_gap {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 ≤
      (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 := by
  have he := (gaussianWeakDbar_deficit_modeTail hn u D hu).2
  have hp := modeTail_nonneg (positiveHermiteModeMass hn u)
    (fun _ => sq_nonneg _)
  linarith

/-- Equality holds exactly when every antiholomorphic mode above degree one vanishes. -/
theorem gaussianWeakDbar_gap_equality_iff {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 =
      ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 ↔
      ∀ d : ℕ, 2 ≤ d → gaussianHermiteMode hn d u = 0 := by
  obtain ⟨ht, he⟩ := gaussianWeakDbar_deficit_modeTail hn u D hu
  constructor
  · intro heq d hd
    have hz : modeTail (positiveHermiteModeMass hn u) = 0 := by linarith
    have hle : ((d - 1 : ℕ) : ℝ) * positiveHermiteModeMass hn u (d - 1) ≤
        modeTail (positiveHermiteModeMass hn u) :=
      ht.le_tsum (d - 1) (fun k _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    rw [hz] at hle
    have hprod : ((d - 1 : ℕ) : ℝ) * positiveHermiteModeMass hn u (d - 1) = 0 :=
      le_antisymm hle (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    have hk : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
    have hm := (mul_eq_zero.mp hprod).resolve_left hk
    have hd1 : d - 1 + 1 = d := by omega
    simp only [positiveHermiteModeMass, hd1] at hm
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gaussianHermiteMode hn d u)])
  · intro hz
    have ht0 : modeTail (positiveHermiteModeMass hn u) = 0 := by
      unfold modeTail
      have hf : (fun k : ℕ => (k : ℝ) * positiveHermiteModeMass hn u k) = fun _ => 0 := by
        funext k
        by_cases hk : k = 0
        · simp [hk]
        · simp [positiveHermiteModeMass, hz (k + 1) (by omega)]
      rw [hf, tsum_zero]
    linarith

/-- The same sharp inequality for ordinary Lebesgue distributional derivatives. -/
theorem gaussianVolumeDistributionalDbar_gap {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianVolumeDistributionalDbar n u (D j) j) :
    ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 ≤
      (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 :=
  gaussianWeakDbar_gap hn u D (fun j => gaussianVolumeDistributionalDbar_weak hn u (D j) j (hu j))

/-- Gaussian antiholomorphic gap with the paper's ordinary Schwartz
 distributional derivative domain and the precise factor `1/n`. -/
theorem gaussianSchwartzDbar_gap {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) :
    ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 ≤
      (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 :=
  gaussianWeakDbar_gap hn u D
    (fun j => (gaussianSchwartzDbar_iff_weak hn u (D j) j).mp (hu j))

/-- Exact equality criterion on the ordinary Schwartz derivative domain. -/
theorem gaussianSchwartzDbar_gap_equality_iff {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) :
    (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 =
      ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 ↔
      ∀ d : ℕ, 2 ≤ d → gaussianHermiteMode hn d u = 0 :=
  gaussianWeakDbar_gap_equality_iff hn u D
    (fun j => (gaussianSchwartzDbar_iff_weak hn u (D j) j).mp (hu j))

/-- A compactly supported entire configuration function vanishes identically. -/
theorem gaussian_entire_compactSupport_eq_zero {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : Differentiable ℂ f) (hc : HasCompactSupport f) :
    f = 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hf.eq_const_of_tendsto_cocompact hc.is_zero_at_infty

/-- Equality in the Gaussian gap forces every first derivative to be
 holomorphic in the genuine distributional sense. -/
theorem gaussianWeakDbar_gap_equality_derivatives_holomorphic {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u (D j) j)
    (heq : (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 =
      ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2) :
    ∀ j k, IsGaussianWeakDbar n (D j) 0 k := by
  have hm := (gaussianWeakDbar_gap_equality_iff hn u D hu).mp heq
  intro j k
  apply gaussianWeakDbar_of_hermiteCoefficient hn (D j) 0 k
  intro pq
  have hd : 2 ≤ totalAntiDegree (raiseHermiteIndex j (raiseHermiteIndex k pq)) := by
    unfold totalAntiDegree raiseHermiteIndex raiseAt
    by_cases hjk : j = k
    · subst k
      have h := Finset.single_le_sum (fun i _ => Nat.zero_le
        (Function.update (Function.update pq.2 j (pq.2 j + 1)) j
          ((Function.update pq.2 j (pq.2 j + 1)) j + 1) i)) (Finset.mem_univ j)
      simpa using (show 2 ≤ _ from le_trans (by simp) h)
    · have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        show (if i = j then 1 else 0) + (if i = k then 1 else 0) ≤
          Function.update (Function.update pq.2 k (pq.2 k + 1)) j
            ((Function.update pq.2 k (pq.2 k + 1)) j + 1) i by
        by_cases hij : i = j <;> by_cases hik : i = k <;>
          simp [hij, hik, hjk, Ne.symm hjk])
      simpa [Finset.sum_add_distrib] using h
  have hi := inner_basis_gaussianHermiteMode hn u
    (totalAntiDegree (raiseHermiteIndex j (raiseHermiteIndex k pq)))
    (raiseHermiteIndex j (raiseHermiteIndex k pq))
  rw [hm _ hd, inner_zero_right, ite_eq_left rfl] at hi
  rw [gaussianWeakDbar_hermiteCoefficient hn u (D j) j (hu j), ← hi]
  simp [gaussianHermiteCoefficient]

/-- The genuine weak antiholomorphic kernel is the actual Hermite zero mode. -/
theorem gaussianWeakDbar_zero_modeZero {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianWeakDbar n u 0 j) : gaussianHermiteMode hn 0 u = u := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode]
  by_cases hd : totalAntiDegree pq = 0
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd]
    obtain ⟨j, hj⟩ : ∃ j : Fin n, 0 < pq.2 j := by
      by_contra h
      push Not at h
      apply hd
      unfold totalAntiDegree
      apply Finset.sum_eq_zero
      intro j _
      exact Nat.eq_zero_of_le_zero (h j)
    let e := raiseHermiteIndexEquivPositive j
    let r : HermiteMultiIndex n := e.symm ⟨pq, hj⟩
    have he : raiseHermiteIndex j r = pq := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨pq, hj⟩)
    have hi := gaussianWeakDbar_hermiteCoefficient hn u 0 j (hu j) r
    rw [he] at hi
    have hk : (Real.sqrt (n * (r.2 j + 1) : ℕ) : ℂ) ≠ 0 := by
      have hp : 0 < (n * (r.2 j + 1) : ℕ) := Nat.mul_pos hn (Nat.succ_pos _)
      exact_mod_cast (Real.sqrt_pos.mpr (show 0 < ((n * (r.2 j + 1) : ℕ) : ℝ) by exact_mod_cast
                                                                                   hp)).ne'
    have hz : gaussianHermiteCoefficient hn u pq = 0 := by
      apply (mul_eq_zero.mp (show (Real.sqrt (n * (r.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn u pq = 0 by simpa [gaussianHermiteCoefficient] using
                                                    hi.symm)).resolve_left hk
    exact hz.symm

/-- A continuous representative of an actual weak-holomorphic Gaussian L²
 class is an entire function on the full configuration space. -/
theorem gaussianWeakDbar_kernel_continuous_entire {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : Continuous f) (hr : (u : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] f)
    (hu : ∀ j, IsGaussianWeakDbar n u 0 j) : Differentiable ℂ f := by
  have he := gaussianZeroMode_has_entire_representative hn u
  rw [gaussianWeakDbar_zero_modeZero hn u hu] at he
  obtain ⟨g, hg, hgr⟩ := he
  have hgf : g = f := continuous_eq_of_ae_eq_complexGaussian hn hg.continuous hf (hgr.trans hr)
  rwa [← hgf]

/-- No nonzero compact smooth function attains equality in the Gaussian
 antiholomorphic gap. -/
theorem gaussianDbar_gap_compact_equality_eq_zero {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (heq : gaussianDbarEnergy n f =
      ‖smoothCompactL2 f (hf.of_le (by simp)) hc‖ ^ 2 -
        ‖gaussianHermiteMode hn 0 (smoothCompactL2 f (hf.of_le (by simp)) hc)‖ ^ 2) :
    f = 0 := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let u := smoothCompactL2 f hf1 hc
  let D := fun j => smoothDbarComponentL2 f hf1 hc j
  have hu (j : Fin n) : IsGaussianWeakDbar n u (D j) j :=
    gaussian_smooth_weak_dbar hn j u (D j) f hf1
      (smoothCompactL2_coeFn f hf1 hc) (smoothDbarComponentL2_coeFn f hf1 hc j)
  have henergy : (1 / (n : ℝ)) * ∑ j : Fin n, ‖D j‖ ^ 2 =
      ‖u‖ ^ 2 - ‖gaussianHermiteMode hn 0 u‖ ^ 2 := by
    rw [sum_norm_sq_smoothDbarComponentL2 hn f hf1 hc]
    exact heq
  have hh := gaussianWeakDbar_gap_equality_derivatives_holomorphic hn u D hu henergy
  have hz (j : Fin n) : dbarComponent f j = 0 := by
    apply gaussian_entire_compactSupport_eq_zero hn
    · exact gaussianWeakDbar_kernel_continuous_entire hn (D j) (dbarComponent f j)
        (continuous_dbarComponent hf1 j) (smoothDbarComponentL2_coeFn f hf1 hc j) (hh j)
    · exact hasCompactSupport_dbarComponent hc j
  have hDz (j : Fin n) : D j = 0 := by
    apply Lp.ext
    filter_upwards [smoothDbarComponentL2_coeFn f hf1 hc j,
      Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hdz hzero
    rw [hdz, hz j, hzero]
  apply gaussian_entire_compactSupport_eq_zero hn f
  · exact gaussianWeakDbar_kernel_continuous_entire hn u f hf.continuous
      (smoothCompactL2_coeFn f hf1 hc) (fun j => by simpa only [hDz j] using hu j)
  · exact hc

theorem gaussianDbar_gap_compact_equality_iff_zero {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    gaussianDbarEnergy n f =
      ‖smoothCompactL2 f (hf.of_le (by simp)) hc‖ ^ 2 -
        ‖gaussianHermiteMode hn 0 (smoothCompactL2 f (hf.of_le (by simp)) hc)‖ ^ 2 ↔ f = 0 := by
  constructor
  · exact gaussianDbar_gap_compact_equality_eq_zero hn f hf hc
  · intro hz
    subst f
    have h0 : smoothCompactL2 (0 : Configuration n → ℂ) (hf.of_le (by simp)) hc = 0 := by
      apply Lp.ext
      exact (smoothCompactL2_coeFn 0 (hf.of_le (by simp)) hc).trans
        (Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)).symm
    rw [h0, gaussianHermiteMode_eq_antiDegreeProjection, map_zero]
    simp [gaussianDbarEnergy, dbarNormSq, dbarComponent]

end
end GinibrePoincare

