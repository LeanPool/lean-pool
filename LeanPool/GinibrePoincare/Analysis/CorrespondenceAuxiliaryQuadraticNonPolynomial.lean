/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryQuadraticNonPolynomial.lean.
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

public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryQuadraticGenerator
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Correspondence auxiliary quadratic non polynomial

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `holomorphicQuadraticSum_generator_not_mixed_polynomial`.
-/

@[expose] public section
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

private def realCollisionPath (n : ℕ) (t : ℝ) : Configuration n :=
  fun j => (t * (j.val : ℝ) : ℝ)

private theorem realCollisionPath_free (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    CollisionFree (realCollisionPath n t) := by
  intro j k he
  have hh : t * (j.val : ℝ) = t * (k.val : ℝ) := Complex.ofReal_injective he
  have hval := mul_left_cancel₀ ht hh
  exact Fin.val_injective (by exact_mod_cast hval)

private theorem realPair_ratio (a : ℝ) (ha : a ≠ 0) :
    ((a : ℂ)^2)/(Complex.normSq (a : ℂ) : ℂ) = 1 := by
  rw [Complex.normSq_ofReal]
  push_cast
  simp [pow_two, mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) (Complex.ofReal_ne_zero.mpr ha)]

private theorem imaginaryPair_ratio (a : ℝ) (ha : a ≠ 0) :
    ((Complex.I*(a : ℂ))^2)/(Complex.normSq (Complex.I*(a : ℂ)) : ℂ) = -1 := by
  rw [Complex.normSq_mul, Complex.normSq_I, one_mul, Complex.normSq_ofReal]
  push_cast
  rw [mul_pow, Complex.I_sq, neg_one_mul]
  simp [pow_two, mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) (Complex.ofReal_ne_zero.mpr ha)]

private theorem quadratic_path_generator (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    complexGinibrePregenerator n holomorphicQuadraticSum (realCollisionPath n t) =
      -4 * holomorphicQuadraticSum (realCollisionPath n t) +
        (4/(n : ℂ))*(vandermondeDegree n : ℂ) := by
  rw [complexGinibrePregenerator_holomorphicQuadraticSum]
  congr 1
  congr 1
  have hr (j k : Fin n) (hk : k ∈ Finset.Ioi j) :
      ((realCollisionPath n t j-realCollisionPath n t k)^2)/
        (Complex.normSq (realCollisionPath n t j-realCollisionPath n t k) : ℂ) = 1 := by
    have hjk : j ≠ k := ne_of_lt (Finset.mem_Ioi.mp hk)
    have hval : (j.val : ℝ) ≠ k.val := by
      intro h
      apply hjk
      apply Fin.val_injective
      exact_mod_cast h
    have ha : t*(j.val : ℝ)-t*(k.val : ℝ) ≠ 0 := by
      rw [←mul_sub]
      exact mul_ne_zero ht (sub_ne_zero.mpr hval)
    simpa only [realCollisionPath,←Complex.ofReal_sub] using realPair_ratio _ ha
  simp_rw [Finset.sum_congr rfl (fun k hk => hr _ k hk)]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [vandermondeDegree_eq_sum_Ioi_card]
  push_cast
  rfl

private theorem quadratic_imaginary_path_generator (n : ℕ) (t : ℝ) (ht : t ≠ 0) :
    complexGinibrePregenerator n holomorphicQuadraticSum
      (fun j => Complex.I * realCollisionPath n t j) =
      -4 * holomorphicQuadraticSum (fun j => Complex.I * realCollisionPath n t j) -
        (4/(n : ℂ))*(vandermondeDegree n : ℂ) := by
  rw [complexGinibrePregenerator_holomorphicQuadraticSum]
  have hr (j k : Fin n) (hk : k ∈ Finset.Ioi j) :
      ((Complex.I*realCollisionPath n t j-Complex.I*realCollisionPath n t k)^2)/
        (Complex.normSq (Complex.I*realCollisionPath n t j-Complex.I*realCollisionPath n t k) : ℂ) =
            -1 := by
    have hjk : j ≠ k := ne_of_lt (Finset.mem_Ioi.mp hk)
    have hval : (j.val : ℝ) ≠ k.val := by
      intro h
      apply hjk
      apply Fin.val_injective
      exact_mod_cast h
    have ha : t*(j.val : ℝ)-t*(k.val : ℝ) ≠ 0 := by
      rw [←mul_sub]
      exact mul_ne_zero ht (sub_ne_zero.mpr hval)
    rw [←mul_sub]
    simpa only [realCollisionPath,←Complex.ofReal_sub] using imaginaryPair_ratio _ ha
  have hs : (∑ j : Fin n, ∑ k ∈ Finset.Ioi j,
      ((Complex.I*realCollisionPath n t j-Complex.I*realCollisionPath n t k)^2)/
        (Complex.normSq (Complex.I*realCollisionPath n t j-Complex.I*realCollisionPath n t k) : ℂ))
            =
        -(vandermondeDegree n : ℂ) := by
    calc
      _ = ∑ j : Fin n, ∑ k ∈ Finset.Ioi j, (-1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        exact hr j k hk
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_neg_one, Finset.sum_neg_distrib]
        rw [vandermondeDegree_eq_sum_Ioi_card]
        push_cast
        rfl
  rw [hs]
  ring

/-- The generator of the paper's symmetric holomorphic quadratic has no
continuous extension from the collision-free domain when `n≥2`. In particular
it cannot agree there with any ordinary polynomial in real/complex coordinates. -/
theorem holomorphicQuadraticSum_generator_no_continuous_extension (n : ℕ)
    (hn : 2 ≤ n) (F : Configuration n → ℂ) (hF : Continuous F) :
    ¬ (∀ z, CollisionFree z → F z =
      complexGinibrePregenerator n holomorphicQuadraticSum z) := by
  intro he
  have hc : Continuous (realCollisionPath n) := by
    apply continuous_pi
    intro j
    exact Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
  have hci : Continuous (fun t : ℝ => fun j : Fin n => Complex.I*realCollisionPath n t j) := by
    apply continuous_pi
    intro j
    exact continuous_const.mul ((continuous_apply j).comp hc)
  have hq : Continuous (holomorphicQuadraticSum : Configuration n → ℂ) := by
    unfold holomorphicQuadraticSum
    fun_prop
  have hr : Set.EqOn (fun t => F (realCollisionPath n t))
      (fun t => -4*holomorphicQuadraticSum (realCollisionPath n t)+
        (4/(n : ℂ))*(vandermondeDegree n : ℂ)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    dsimp only
    rw [he _ (realCollisionPath_free n t (ne_of_gt ht)), quadratic_path_generator n t (ne_of_gt ht)]
  have hi : Set.EqOn (fun t => F (fun j => Complex.I*realCollisionPath n t j))
      (fun t => -4*holomorphicQuadraticSum (fun j => Complex.I*realCollisionPath n t j)-
        (4/(n : ℂ))*(vandermondeDegree n : ℂ)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    have hfree : CollisionFree (fun j => Complex.I*realCollisionPath n t j) := by
      intro j k heq
      exact realCollisionPath_free n t (ne_of_gt ht)
        (mul_left_cancel₀ Complex.I_ne_zero heq)
    dsimp only
    rw [he _ hfree, quadratic_imaginary_path_generator n t (ne_of_gt ht)]
  have hzero : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact le_rfl
  have hr0 := hr.closure (hF.comp hc) (by fun_prop) hzero
  have hi0 := hi.closure (hF.comp hci) (by fun_prop) hzero
  dsimp only at hr0 hi0
  simp only [realCollisionPath, zero_mul, Complex.ofReal_zero, mul_zero,
    holomorphicQuadraticSum, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_add, zero_sub] at hr0 hi0
  have hzpath : realCollisionPath n 0 = fun _ => 0 := by
    funext j
    simp [realCollisionPath]
  rw [hzpath] at hr0
  have hvpos : 0 < vandermondeDegree n := by
    rw [vandermondeDegree_eq_sum_Ioi_card]
    have hi : (Finset.Ioi (⟨0, by omega⟩ : Fin n)).card > 0 := by
      apply Finset.card_pos.mpr
      exact ⟨⟨1, by omega⟩, by simp⟩
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i : Fin n => (Finset.Ioi i).card)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨0, by omega⟩ : Fin n)))
  have hneq : (4/(n : ℂ))*(vandermondeDegree n : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact div_ne_zero (by norm_num) (by exact_mod_cast (show n ≠ 0 by omega))
    · exact_mod_cast hvpos.ne'
  have hh : (4/(n : ℂ))*(vandermondeDegree n : ℂ) =
      -((4/(n : ℂ))*(vandermondeDegree n : ℂ)) := hr0.symm.trans hi0
  exact hneq (by linear_combination (1/2 : ℂ) * hh)

/-- Literal non-polynomial conclusion, allowing both holomorphic and
antiholomorphic variables, on precisely the collision-free paper domain. -/
theorem holomorphicQuadraticSum_generator_not_mixed_polynomial (n : ℕ)
    (hn : 2 ≤ n) (P : MvPolynomial (Fin n × Fin 2) ℂ) :
    ¬ (∀ z : Configuration n, CollisionFree z →
      complexGinibrePregenerator n holomorphicQuadraticSum z =
        MvPolynomial.eval (fun k : Fin n × Fin 2 =>
          if k.2 = 0 then z k.1 else conj (z k.1)) P) := by
  intro h
  apply holomorphicQuadraticSum_generator_no_continuous_extension n hn
    (fun z : Configuration n => MvPolynomial.eval
      (fun k : Fin n × Fin 2 => if k.2 = 0 then z k.1 else conj (z k.1)) P)
  · apply (MvPolynomial.continuous_eval P).comp
    apply continuous_pi
    intro k
    by_cases hk : k.2 = 0
    · simp only [hk, ite_true]
      exact continuous_apply k.1
    · simp only [hk, ite_false]
      exact Complex.continuous_conj.comp (continuous_apply k.1)
  · intro z hz
    exact (h z hz).symm

end
end GinibrePoincare
