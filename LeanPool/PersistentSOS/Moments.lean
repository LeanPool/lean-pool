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

public import LeanPool.PersistentSOS.MomentData
public import LeanPool.PersistentSOS.MomentBridge
public import LeanPool.PersistentSOS.QuadraticMonomials
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A positive sphere moment functional with strict cubic separation

The rational moment table is interpreted on ordinary multivariate polynomials.
Positivity follows from the exact finite block certificates and complete
coverage of all monomials of total degree at most two.
-/


@[expose] public section

namespace PersistentSOS

open scoped BigOperators


/-- Indices of the complete quadratic monomial basis across all eight blocks. -/
abbrev MomentIndex := (c : Fin 8) × Fin (blockSize c)

/-- The normalized exact moment functional separating the cubic from its sphere bound. -/
noncomputable def sphereFunctional : Poly →ₗ[ℝ] ℝ := momentLinearMap momentNumerator

@[simp] theorem sphereFunctional_monomial (d : Exponent) (c : ℝ) :
    sphereFunctional (MvPolynomial.monomial d c) =
      c * (momentNumerator (exponentKey d) : ℝ) / 1000000000 :=
  momentLinearMap_monomial _ _ _

theorem basisPair_covers : ∀ i j : Fin 15, ∃ b : MomentIndex,
    basisPair b.1 b.2 = (i, j) ∨ basisPair b.1 b.2 = (j, i) := by
  decide +kernel

@[simp] theorem variableExponent_zero : variableExponent 0 = 0 := by
  simp [variableExponent]

@[simp] theorem variableExponent_succ (i : Fin 14) :
    variableExponent i.succ = Finsupp.single i 1 := by
  simp [variableExponent, Fin.succ_ne_zero]

theorem momentBasis_zero : ∃ b : MomentIndex, momentBasis b = 0 := by
  obtain ⟨b, h | h⟩ := basisPair_covers 0 0
  all_goals exact ⟨b, by simp [momentBasis, h]⟩

theorem momentBasis_single (i : Fin 14) :
    ∃ b : MomentIndex, momentBasis b = Finsupp.single i 1 := by
  obtain ⟨b, h | h⟩ := basisPair_covers 0 i.succ
  · exact ⟨b, by simp [momentBasis, h]⟩
  · exact ⟨b, by simp [momentBasis, h]⟩

theorem momentBasis_pair (i j : Fin 14) :
    ∃ b : MomentIndex, momentBasis b = Finsupp.single i 1 + Finsupp.single j 1 := by
  obtain ⟨b, h | h⟩ := basisPair_covers i.succ j.succ
  · exact ⟨b, by simp [momentBasis, h]⟩
  · exact ⟨b, by simp [momentBasis, h, add_comm]⟩

theorem momentBasis_covers (d : Exponent) (hd : d.sum (fun _ n => n) ≤ 2) :
    ∃ b : MomentIndex, momentBasis b = d := by
  rcases exponent_degree_le_two d hd with h | ⟨i, h⟩ | ⟨i, j, h⟩
  · simpa [h] using momentBasis_zero
  · simpa [h] using momentBasis_single i
  · simpa [h] using momentBasis_pair i j

lemma moment_inner_sum (x : MomentIndex → ℝ) (c : Fin 8) (i : Fin (blockSize c)) :
    (∑ d : Fin 8, ∑ j : Fin (blockSize d), x ⟨c, i⟩ *
      (momentNumerator (basisKey c i + basisKey d j) : ℝ) * x ⟨d, j⟩) =
    ∑ j : Fin (blockSize c), x ⟨c, i⟩ * (blockNumerator c i j : ℝ) * x ⟨c, j⟩ := by
  rw [Finset.sum_eq_single c]
  · simp only [moment_block]
  · intro d _ hdc
    simp only [moment_cross c d hdc.symm, Int.cast_zero, mul_zero, zero_mul, Finset.sum_const_zero]
  · simp

lemma moment_gram_nonneg (x : MomentIndex → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * sphereFunctional
      (MvPolynomial.monomial (momentBasis i + momentBasis j) 1) * x j := by
  simp only [sphereFunctional_monomial, one_mul, exponentKey_add, exponentKey_momentBasis]
  have hnum : (∑ i : MomentIndex, ∑ j : MomentIndex,
      x i * (momentNumerator (basisKey i.1 i.2 + basisKey j.1 j.2) : ℝ) * x j) =
      ∑ c : Fin 8, quadraticForm (fun i j => (blockNumerator c i j : ℝ))
        (fun i => x ⟨c, i⟩) := by
    simp only [Fintype.sum_sigma, quadraticForm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro i _
    exact moment_inner_sum x c i
  have hpos : 0 ≤ ∑ i : MomentIndex, ∑ j : MomentIndex,
      x i * (momentNumerator (basisKey i.1 i.2 + basisKey j.1 j.2) : ℝ) * x j := by
    rw [hnum]
    exact block_nonneg blockSize (fun c i j => (blockNumerator c i j : ℝ))
      blockNumerator_psd x
  convert div_nonneg hpos (by norm_num : (0:ℝ) ≤ 1000000000) using 1
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem moment_square_nonneg (h : Poly) (hd : h.totalDegree ≤ 2) :
    0 ≤ sphereFunctional (h ^ 2) :=
  nonneg_quadratic_square_of_momentMatrix momentBasis momentBasis_covers sphereFunctional
    moment_gram_nonneg h hd

theorem moment_one : sphereFunctional 1 = 1 := by
  change sphereFunctional (MvPolynomial.monomial 0 1) = 1
  rw [sphereFunctional_monomial, exponentKey_zero]
  norm_num [momentNumerator]

theorem moment_q : sphereFunctional qPoly = 1 := by
  simp only [qPoly, map_sum, MvPolynomial.X_pow_eq_monomial,
    sphereFunctional_monomial, exponentKey_single, one_mul]
  have h : (∑ i : Fin 14, (momentNumerator (2 * 5 ^ i.val) : ℝ)) = 1000000000 := by
    exact_mod_cast moment_quadratic_numerator_sum
  rw [← Finset.sum_div, h]
  norm_num

theorem moment_q_sq : sphereFunctional (qPoly ^ 2) = 1 := by
  rw [pow_two]
  simp only [qPoly, Finset.sum_mul, Finset.mul_sum, map_sum,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
    sphereFunctional_monomial, exponentKey_add, exponentKey_single, one_mul]
  have h : (∑ i : Fin 14, ∑ j : Fin 14,
      (momentNumerator (2 * 5 ^ i.val + 2 * 5 ^ j.val) : ℝ)) = 1000000000 := by
    exact_mod_cast moment_quartic_numerator_sum
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm, h]
  norm_num

theorem moment_cubic : sphereFunctional cubicPoly = 500753357629 / 500000000000 := by
  have h3 : (3 : Poly) = MvPolynomial.C (3 : ℝ) :=
    (map_natCast MvPolynomial.C 3).symm
  simp only [cubicPoly, map_add, map_sub, MvPolynomial.X_pow_eq_monomial]
  simp only [h3, MvPolynomial.X, MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul_monomial]
  simp only [sphereFunctional_monomial, exponentKey_add, exponentKey_single]
  norm_num [momentNumerator]

end PersistentSOS
