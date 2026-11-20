/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberSquareRoot.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSpectralSelfAdjoint
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberWeakDomain
/-!
# Correspondence operator number square root

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_sqrt_isSelfAdjoint`,
`correspondenceOperatorNumber_sqrt_square_graph_iff`,
`correspondenceOperatorNumber_shifted_sqrt_paper_energy`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
/-- The maximal Hermite spectral square root is genuinely self-adjoint. -/
theorem correspondenceOperatorNumber_sqrt_isSelfAdjoint (n : ℕ) (hn : 0 < n) :
    IsSelfAdjoint (correspondenceOperatorNumberSpectral n hn Real.sqrt) :=
  correspondenceOperatorNumberSpectral_isSelfAdjoint n hn Real.sqrt Real.sqrt_nonneg

/-- The full graph composition of the spectral square root equals the actual
maximal number operator, including both operator domains. -/
theorem correspondenceOperatorNumber_sqrt_square_graph_iff (n : ℕ) (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) :
    (u, v)∈(correspondenceOperatorNumber n hn).graph ↔
      ∃w, (u, w)∈(correspondenceOperatorNumberSpectral n hn Real.sqrt).graph ∧
        (w, v)∈(correspondenceOperatorNumberSpectral n hn Real.sqrt).graph := by
  have hs (pq : HermiteMultiIndex n) : (Real.sqrt (n*totalAntiDegree pq : ℕ) : ℂ)^2=
      (n*totalAntiDegree pq : ℕ) := by
    have hh := congrArg (fun x : ℝ=>(x : ℂ)) (Real.sq_sqrt (Nat.cast_nonneg (n*totalAntiDegree pq)))
    simpa using hh
  constructor
  · intro huv
    choose D hD using correspondenceOperatorNumber_weak_dbar_exists hn u v huv
    obtain ⟨w, hw⟩ := (correspondenceOperatorNumber_sqrt_domain_iff_ordinary_form hn u).mpr ⟨D, hD⟩
    refine ⟨w, hw,?_⟩
    rw [correspondenceOperatorNumberSpectral_graph] at hw ⊢
    rw [correspondenceOperatorNumber_graph] at huv
    intro pq
    rw [huv pq, hw pq,← mul_assoc,← pow_two, hs]
  · rintro ⟨w, hw, hv⟩
    rw [correspondenceOperatorNumberSpectral_graph] at hw hv
    rw [correspondenceOperatorNumber_graph]
    intro pq
    rw [hv pq, hw pq,← mul_assoc,← pow_two, hs]

/-- Exact spectral shifted-square norm (6.13) on the literal holomorphic
complement and full ordinary Gaussian form domain. -/
theorem correspondenceOperatorNumber_shifted_sqrt_energy {n : ℕ} (hn : 0 < n)
    (u s : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, IsGaussianWeakDbar n u (D j) j)
    (hu : gaussianHermiteMode hn 0 u = 0)
    (hs : (u, s) ∈ (correspondenceOperatorNumberSpectral n hn (fun x => Real.sqrt (x - n))).graph) :
    (∑j : Fin n, ‖D j‖^2)=(n : ℝ)*‖u‖^2+‖s‖^2 := by
  rw [correspondenceOperatorNumberSpectral_graph] at hs
  have hE := correspondenceOperatorNumber_ordinary_form_hasSum hn u D hD
  have hU := (hasSum_norm_sq_gaussianHermiteCoefficient hn u).mul_left (n : ℝ)
  have hSub := hE.sub hU
  have hS := hasSum_norm_sq_gaussianHermiteCoefficient hn s
  have he (pq : HermiteMultiIndex n) : ‖gaussianHermiteCoefficient hn s pq‖^2=
      ((n*totalAntiDegree pq : ℕ) : ℝ)*‖gaussianHermiteCoefficient hn u pq‖^2-
        (n : ℝ)*‖gaussianHermiteCoefficient hn u pq‖^2 := by
    rw [hs pq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    by_cases hd : totalAntiDegree pq=0
    · have hc := inner_basis_gaussianHermiteMode hn u 0 pq
      rw [hu, inner_zero_right, ite_eq_left hd] at hc
      have hz : gaussianHermiteCoefficient hn u pq=0 := by
        simpa only [gaussianHermiteCoefficient_eq_inner] using hc.symm
      simp [hz]
    · have hnq : (n : ℝ)≤((n*totalAntiDegree pq : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd)
      rw [Real.sq_sqrt (sub_nonneg.mpr hnq)]
      ring
  have hv : ‖s‖^2=(∑j : Fin n, ‖D j‖^2)-(n : ℝ)*‖u‖^2 :=
    hS.unique (hSub.congr_fun (fun pq=>he pq))
  linarith
/-- Every ordinary Gaussian form vector belongs to the maximal shifted
square-root domain; the holomorphic complement has the exact paper energy. -/
theorem correspondenceOperatorNumber_shifted_sqrt_exists {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, IsGaussianWeakDbar n u (D j) j) :
    ∃s, (u, s)∈(correspondenceOperatorNumberSpectral n hn (fun x=>Real.sqrt (x-n))).graph := by
  apply (correspondenceOperatorNumberSpectral_domain_iff n hn _ u).mpr
  apply Summable.of_nonneg_of_le (fun _=>sq_nonneg _) _
    (correspondenceOperatorNumber_ordinary_form_hasSum hn u D hD).summable
  intro pq
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  by_cases h : 0≤((n*totalAntiDegree pq : ℕ) : ℝ)-(n : ℝ)
  · rw [Real.sq_sqrt h]
    exact sub_le_self _ (Nat.cast_nonneg n)
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    simpa using (Nat.cast_nonneg (n*totalAntiDegree pq) : (0 : ℝ)≤_)

theorem correspondenceOperatorNumber_shifted_sqrt_paper_energy {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, IsGaussianWeakDbar n u (D j) j)
    (hu : gaussianHermiteMode hn 0 u = 0) :
    ∃s, (u, s)∈(correspondenceOperatorNumberSpectral n hn (fun x=>Real.sqrt (x-n))).graph ∧
      (∑j : Fin n, ‖D j‖^2)=(n : ℝ)*‖u‖^2+‖s‖^2 := by
  obtain ⟨s, hs⟩ := correspondenceOperatorNumber_shifted_sqrt_exists hn u D hD
  exact ⟨s, hs, correspondenceOperatorNumber_shifted_sqrt_energy hn u s D hD hu hs⟩
end
end GinibrePoincare
