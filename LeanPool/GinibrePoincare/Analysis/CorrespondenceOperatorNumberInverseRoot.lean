/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberInverseRoot.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSquareRoot
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberBochnerClosure
/-!
# Correspondence operator number inverse root

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_inverse_sqrt_second_energy`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem correspondenceOperatorNumber_sqrt_form_energy {n : ℕ} (hn : 0 < n)
    (u s : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, IsGaussianWeakDbar n u (D j) j)
    (hs : (u, s) ∈ (correspondenceOperatorNumberSpectral n hn Real.sqrt).graph) :
    ‖s‖^2=∑j : Fin n, ‖D j‖^2 := by
  rw [correspondenceOperatorNumberSpectral_graph] at hs
  apply (hasSum_norm_sq_gaussianHermiteCoefficient hn s).unique
  apply (correspondenceOperatorNumber_ordinary_form_hasSum hn u D hD).congr_fun
  intro pq
  rw [hs pq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

theorem correspondenceOperatorNumber_inverse_sqrt_graph {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : gaussianHermiteMode hn 0 u = 0) :
    (gaussianHermiteInverseSquareRoot hn u, u)∈
      (correspondenceOperatorNumberSpectral n hn Real.sqrt).graph := by
  rw [correspondenceOperatorNumberSpectral_graph]
  intro pq
  rw [gaussianHermiteCoefficient_inverseSquareRoot]
  by_cases hd : totalAntiDegree pq=0
  · have hc := inner_basis_gaussianHermiteMode hn u 0 pq
    rw [hu, inner_zero_right, ite_eq_left hd] at hc
    have hz : gaussianHermiteCoefficient hn u pq=0 := by
      simpa only [gaussianHermiteCoefficient_eq_inner] using hc.symm
    simp [hd, hz]
  · have hnq : (0 : ℝ)<(n*totalAntiDegree pq : ℕ) := by
      exact_mod_cast Nat.mul_pos hn (Nat.pos_of_ne_zero hd)
    have hsq : (Real.sqrt (n*totalAntiDegree pq : ℕ) : ℂ)≠0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hnq).ne'
    unfold hermiteInverseSquareRootWeight
    push_cast
    simp only [Nat.cast_mul] at hsq
    rw [← mul_assoc, mul_inv_cancel₀ hsq, one_mul]

/-- Literal (6.15–16): inverse square root of a full ordinary form vector
lies in the genuine maximal number domain; its genuine second derivatives
have exactly the shifted-square-root norm. -/
theorem correspondenceOperatorNumber_inverse_sqrt_second_energy {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, IsGaussianWeakDbar n u (D j) j)
    (hu : gaussianHermiteMode hn 0 u = 0) :
    ∃w s : Lp ℂ 2 (complexGaussianMeasure n),
    ∃V : Fin n→Lp ℂ 2 (complexGaussianMeasure n),
    ∃Q : Fin n→Fin n→Lp ℂ 2 (complexGaussianMeasure n),
      (gaussianHermiteInverseSquareRoot hn u, w)∈(correspondenceOperatorNumber n hn).graph ∧
      (u, s)∈(correspondenceOperatorNumberSpectral n hn (fun x=>Real.sqrt (x-n))).graph ∧
      (∀j, IsGaussianWeakDbar n (gaussianHermiteInverseSquareRoot hn u) (V j) j) ∧
      (∀j k, IsGaussianWeakDbar n (V j) (Q j k) k) ∧
      ‖s‖^2=‖w‖^2-(n : ℝ)*(∑j : Fin n, ‖V j‖^2) ∧
      ‖s‖^2=∑j : Fin n,∑k : Fin n, ‖Q j k‖^2 := by
  obtain ⟨w, hw⟩ := (correspondenceOperatorNumber_sqrt_domain_iff_ordinary_form hn u).mpr ⟨D, hD⟩
  have hv := correspondenceOperatorNumber_inverse_sqrt_graph hn u hu
  have hN := (correspondenceOperatorNumber_sqrt_square_graph_iff n hn
    (gaussianHermiteInverseSquareRoot hn u) w).mpr ⟨u, hv, hw⟩
  obtain ⟨V, Q, hV, hQ, hBK⟩ := correspondenceOperatorNumber_full_bochner_kodaira hn
    (gaussianHermiteInverseSquareRoot hn u) w hN
  obtain ⟨s, hs, hE⟩ := correspondenceOperatorNumber_shifted_sqrt_paper_energy hn u D hD hu
  have hWu := correspondenceOperatorNumber_sqrt_form_energy hn u w D hD hw
  have hVu := correspondenceOperatorNumber_sqrt_form_energy hn
    (gaussianHermiteInverseSquareRoot hn u) u V hV hv
  refine ⟨w, s, V, Q, hN, hs, hV, hQ,?_,?_⟩ <;> nlinarith
end
end GinibrePoincare
