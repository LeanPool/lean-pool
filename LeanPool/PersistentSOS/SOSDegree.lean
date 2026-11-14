/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

/-
Adapted from JD-Jones-ASES/persistent-sos, commit
d432ff9a67594cc0fa7a7af1913320b46d2a86db.
Original MIT notice (retained under the permission to sublicense):

MIT License

Copyright (c) 2026 JD Jones

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

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Basic.Real.Basic

/-! # Degree bounds for ordinary sums of squares

A finite sum of squares of real polynomials cannot cancel its highest
terms. Consequently, every summand of an SOS polynomial of degree at most
`2 * d` has degree at most `d`. The SOS representations in this result
are unrestricted ordinary polynomial representations.
-/


public section

namespace PersistentSOS

open MvPolynomial
open scoped BigOperators MonomialOrder

private theorem degree_add_of_nonneg_leadingCoeff {σ : Type*}
    (m : MonomialOrder σ) (f g : MvPolynomial σ ℝ)
    (hf : 0 ≤ m.leadingCoeff f) (hg : 0 ≤ m.leadingCoeff g) :
    m.toSyn (m.degree (f + g)) =
      m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) ∧
      0 ≤ m.leadingCoeff (f + g) := by
  rcases lt_trichotomy (m.toSyn (m.degree f)) (m.toSyn (m.degree g)) with h | h | h
  · constructor
    · rw [m.degree_add_eq_right_of_lt h, sup_eq_right.mpr h.le]
    · rw [add_comm, m.leadingCoeff_add_of_lt h]
      exact hg
  · have heq : m.degree f = m.degree g := m.toSyn.injective h
    by_cases hf0 : f = 0
    · simp_all
    have hpos : 0 < m.leadingCoeff f :=
      lt_of_le_of_ne hf (Ne.symm (m.leadingCoeff_ne_zero_iff.mpr hf0))
    have hcoeff : (f + g).coeff (m.degree f) ≠ 0 := by
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      simpa only [MonomialOrder.leadingCoeff, heq] using
        ne_of_gt (add_pos_of_pos_of_nonneg hpos hg)
    have hd : m.degree (f + g) = m.degree f := by
      apply m.toSyn.injective
      apply le_antisymm
      · exact m.degree_add_le.trans (by simp [h])
      · exact m.le_degree (mem_support_iff.mpr hcoeff)
    constructor
    · simp [hd, h]
    · rw [MonomialOrder.leadingCoeff, hd, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      simpa only [MonomialOrder.leadingCoeff, heq] using add_nonneg hf hg
  · constructor
    · rw [m.degree_add_of_lt h, sup_eq_left.mpr h.le]
    · rw [m.leadingCoeff_add_of_lt h]
      exact hf

private theorem degree_sum_of_nonneg_leadingCoeff {σ ι : Type*}
    (m : MonomialOrder σ) (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (hf : ∀ i ∈ s, 0 ≤ m.leadingCoeff (f i)) :
    m.toSyn (m.degree (∑ i ∈ s, f i)) = s.sup (fun i => m.toSyn (m.degree (f i))) ∧
      0 ≤ m.leadingCoeff (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have his := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hadd := degree_add_of_nonneg_leadingCoeff m (f i) (∑ j ∈ s, f j)
      (hf i (Finset.mem_insert_self i s)) his.2
    simpa [Finset.sum_insert hi, Finset.sup_insert, his.1] using hadd

/-- Each square in an ordinary finite sum of squares has total degree no
larger than the sum. This includes representations with arbitrary - degree
polynomial summands. -/
theorem totalDegree_sq_le_sum_sq {σ ι : Type*} [LinearOrder σ] [WellFoundedGT σ]
    (s : Finset ι) (f : ι → MvPolynomial σ ℝ) {i : ι} (hi : i ∈ s) :
    (f i ^ 2).totalDegree ≤ (∑ j ∈ s, f j ^ 2).totalDegree := by
  classical
  have hsum := degree_sum_of_nonneg_leadingCoeff MonomialOrder.degLex s
    (fun j => f j ^ 2) (by
      intro j hj
      rw [MonomialOrder.leadingCoeff_pow]
      exact sq_nonneg _)
  apply degLex_totalDegree_monotone
  rw [hsum.1]
  exact Finset.le_sup (f := fun j => MonomialOrder.degLex.toSyn (MonomialOrder.degLex.degree (f j
    ^ 2))) hi

/-- Ordinary SOS degree bridge, valid for every even total - degree bound. -/
theorem totalDegree_le_of_sum_sq {σ ι : Type*} [LinearOrder σ] [WellFoundedGT σ]
    (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (d : ℕ)
    (h : (∑ j ∈ s, f j ^ 2).totalDegree ≤ 2 * d) {i : ι} (hi : i ∈ s) :
    (f i).totalDegree ≤ d := by
  by_cases hi0 : f i = 0
  · simp [hi0]
  have hsq := (totalDegree_sq_le_sum_sq s f hi).trans h
  rw [pow_two, totalDegree_mul_of_isDomain hi0 hi0] at hsq
  omega

/-- In particular, every summand in any ordinary quartic SOS
representation is a polynomial of total degree at most two. -/
theorem quartic_sos_summand_degree {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]
    {p : MvPolynomial σ ℝ} (hp : p.totalDegree ≤ 4)
    {m : ℕ} {f : Fin m → MvPolynomial σ ℝ} (h : p = ∑ i, f i ^ 2) (i : Fin m) :
    (f i).totalDegree ≤ 2 := by
  apply totalDegree_le_of_sum_sq Finset.univ f 2
  · simpa [← h] using hp
  · exact Finset.mem_univ i

end PersistentSOS
