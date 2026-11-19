/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUActionExpansion.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionEnergy

/-! Exact interaction form of the OU-relative Hamiltonian action. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreInteractionGradientNormSq_continuousOn (n : ℕ) :
    ContinuousOn (ginibreInteractionGradientNormSq n) {z | CollisionFree z} := by
  have hV : ContDiffOn ℝ ∞ (ginibreInteractionPotential n) {z | CollisionFree z} :=
    fun z hz => (ginibreInteractionPotential_contDiffAt n z hz).contDiffWithinAt
  have hd := hV.continuousOn_fderiv_of_isOpen (isOpen_collisionFree n) (by simp)
  unfold ginibreInteractionGradientNormSq
  apply continuousOn_finsetSum
  intro j hj
  exact (hd.clm_apply continuous_const.continuousOn).pow 2 |>.add
    ((hd.clm_apply continuous_const.continuousOn).pow 2)

theorem ginibreHamiltonianGradientNormSq_path_integral {n : ℕ}
    (T : ℝ) (hT : 0 ≤ T) (x : ℝ → Configuration n)
    (hx : ContinuousOn x (Icc 0 T)) (hCF : ∀ s ∈ Icc 0 T, CollisionFree (x s)) :
    (∫ s in (0 : ℝ)..T, ginibreHamiltonianGradientNormSq n (x s)) =
      4*(n : ℝ)^2*(∫ s in (0 : ℝ)..T, configurationNormSq (x s))-
      4*(n : ℝ)*(2*vandermondeDegree n : ℕ)*T+
      (∫ s in (0 : ℝ)..T, ginibreInteractionGradientNormSq n (x s)) := by
  have hN : IntervalIntegrable (fun s => configurationNormSq (x s)) volume 0 T :=
    ((contDiff_configurationNormSq (n := n)).continuous.comp_continuousOn
        hx).intervalIntegrable_of_Icc hT
  have hV : IntervalIntegrable (fun s => ginibreInteractionGradientNormSq n (x s)) volume 0 T :=
    ((ginibreInteractionGradientNormSq_continuousOn n).comp hx hCF).intervalIntegrable_of_Icc hT
  have he : (∫ s in (0 : ℝ)..T, ginibreHamiltonianGradientNormSq n (x s)) =
      ∫ s in (0 : ℝ)..T, 4*(n : ℝ)^2*configurationNormSq (x s)-
        4*(n : ℝ)*(2*vandermondeDegree n : ℕ)+ginibreInteractionGradientNormSq n (x s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    exact ginibreHamiltonianGradientNormSq_interaction _ (hCF s hs)
  rw [he, intervalIntegral.integral_add ((hN.const_mul _).sub intervalIntegrable_const) hV,
    intervalIntegral.integral_sub (hN.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem ginibreHamiltonianOUPathQuotient_expansion {n : ℕ} (hn : 0 < n)
    (α T : ℝ) (hT : 0 ≤ T) (x : ℝ → Configuration n)
    (hx : ContinuousOn x (Icc 0 T)) (hCF : ∀ s ∈ Icc 0 T, CollisionFree (x s)) :
    ginibreHamiltonianGradientPathWeight n α T x / ginibreQuadraticGradientPathWeight n α T x =
      Real.exp (-(ginibreInteractionPotential n (x 0)+ginibreInteractionPotential n (x T))/2+
        (α/(n : ℝ))*(2*vandermondeDegree n : ℕ)*T-
        (α/(4*(n : ℝ)^2))*(∫ s in (0 : ℝ)..T, ginibreInteractionGradientNormSq n (x s))) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (z : Configuration n) : ginibreHamiltonian n z =
      (n : ℝ)*configurationNormSq z+ginibreInteractionPotential n z := by
    unfold ginibreHamiltonian ginibreInteractionPotential
    ring
  unfold ginibreHamiltonianGradientPathWeight ginibreQuadraticGradientPathWeight
      ginibreHamiltonianPathEnergy
  rw [← Real.exp_sub, ginibreHamiltonianGradientNormSq_path_integral T hT x hx hCF, he, he]
  congr 1
  field_simp
  ring

theorem ginibreHamiltonianOUPathQuotient_le_endpoint {n : ℕ} (hn : 0 < n)
    (α T : ℝ) (hα : 0 ≤ α) (hT : 0 ≤ T) (x : ℝ → Configuration n)
    (hx : ContinuousOn x (Icc 0 T)) (hCF : ∀ s ∈ Icc 0 T, CollisionFree (x s)) :
    ginibreHamiltonianGradientPathWeight n α T x / ginibreQuadraticGradientPathWeight n α T x ≤
      Real.exp (-(ginibreInteractionPotential n (x 0)+ginibreInteractionPotential n (x T))/2+
        (α/(n : ℝ))*(2*vandermondeDegree n : ℕ)*T) := by
  rw [ginibreHamiltonianOUPathQuotient_expansion hn α T hT x hx hCF]
  apply Real.exp_le_exp.mpr
  apply sub_le_self
  apply mul_nonneg (div_nonneg hα (by positivity))
  apply intervalIntegral.integral_nonneg_of_forall hT
  intro s
  exact Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem ginibreHamiltonianOUPathQuotient_sq_le_vandermonde {n : ℕ} (hn : 0 < n)
    (α T : ℝ) (hα : 0 ≤ α) (hT : 0 ≤ T) (x : ℝ → Configuration n)
    (hx : ContinuousOn x (Icc 0 T)) (hCF : ∀ s ∈ Icc 0 T, CollisionFree (x s)) :
    (ginibreHamiltonianGradientPathWeight n α T x / ginibreQuadraticGradientPathWeight n α T x)^2 ≤
      vandermondeWeight (x 0)*vandermondeWeight (x T)*
        Real.exp (2*(α/(n : ℝ))*(2*vandermondeDegree n : ℕ)*T) := by
  have hp : 0 ≤ ginibreHamiltonianGradientPathWeight n α T x /
      ginibreQuadraticGradientPathWeight n α T x :=
    div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have h := pow_le_pow_left₀ hp
    (ginibreHamiltonianOUPathQuotient_le_endpoint hn α T hα hT x hx hCF) 2
  refine h.trans_eq ?_
  have he0 : Real.exp (-ginibreInteractionPotential n (x 0)) = vandermondeWeight (x 0) := by
    unfold ginibreInteractionPotential
    rw [neg_neg, Real.exp_log (vandermondeWeight_pos_of_collisionFree _ (hCF 0 ⟨le_rfl, hT⟩))]
  have heT : Real.exp (-ginibreInteractionPotential n (x T)) = vandermondeWeight (x T) := by
    unfold ginibreInteractionPotential
    rw [neg_neg, Real.exp_log (vandermondeWeight_pos_of_collisionFree _ (hCF T ⟨hT, le_rfl⟩))]
  rw [pow_two,← Real.exp_add]
  rw [← he0,← heT,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

end
end GinibrePoincare
