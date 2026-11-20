/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberShiftedRoot.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberCfcRoot
/-!
# Correspondence operator number shifted root

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_shifted_sqrt_square_graph_iff`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- On the literal holomorphic orthogonal complement, the genuine maximal
shifted root squares to N−nI, with the full graph domains preserved. -/
theorem correspondenceOperatorNumber_shifted_sqrt_square_graph_iff (n : ℕ) (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) (hu : gaussianHermiteMode hn 0 u = 0) :
    (u, v+(n : ℂ) • u)∈(correspondenceOperatorNumber n hn).graph ↔
      ∃w, (u, w)∈(correspondenceOperatorNumberSpectral n hn (fun x=>Real.sqrt (x-n))).graph ∧
        (w, v)∈(correspondenceOperatorNumberSpectral n hn (fun x=>Real.sqrt (x-n))).graph := by
  have hz (pq : HermiteMultiIndex n) (hd : totalAntiDegree pq=0) :
      gaussianHermiteCoefficient hn u pq=0 := by
    have hc := inner_basis_gaussianHermiteMode hn u 0 pq
    rw [hu, inner_zero_right, ite_eq_left hd] at hc
    simpa only [gaussianHermiteCoefficient_eq_inner] using hc.symm
  have he (pq : HermiteMultiIndex n) (hd : totalAntiDegree pq≠0) :
      (Real.sqrt (((n*totalAntiDegree pq : ℕ) : ℝ)-n) : ℂ)^2=
        ((n*totalAntiDegree pq : ℕ) : ℂ)-(n : ℂ) := by
    have hh : (n : ℝ)≤((n*totalAntiDegree pq : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_right n (Nat.pos_of_ne_zero hd)
    have hs := congrArg (fun x : ℝ=>(x : ℂ)) (Real.sq_sqrt (sub_nonneg.mpr hh))
    simpa using hs
  constructor
  · intro hN
    choose D hD using correspondenceOperatorNumber_weak_dbar_exists hn u (v+(n : ℂ) • u) hN
    obtain ⟨w, hw⟩ := correspondenceOperatorNumber_shifted_sqrt_exists hn u D hD
    refine ⟨w, hw,?_⟩
    rw [correspondenceOperatorNumberSpectral_graph] at hw ⊢
    rw [correspondenceOperatorNumber_graph] at hN
    intro pq
    have hc := hN pq
    simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right, inner_smul_right] at hc
    simp only [← gaussianHermiteCoefficient_eq_inner] at hc
    rw [hw pq,← mul_assoc,← pow_two]
    by_cases hd : totalAntiDegree pq=0
    · rw [hz pq hd] at hc ⊢
      simpa using hc
    · rw [he pq hd]
      linear_combination hc
  · rintro ⟨w, hw, hv⟩
    rw [correspondenceOperatorNumberSpectral_graph] at hw hv
    rw [correspondenceOperatorNumber_graph]
    intro pq
    simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right, inner_smul_right]
    simp only [← gaussianHermiteCoefficient_eq_inner]
    rw [hv pq, hw pq,← mul_assoc,← pow_two]
    by_cases hd : totalAntiDegree pq=0
    · simp [hz pq hd]
    · rw [he pq hd]
      ring
end
end GinibrePoincare
