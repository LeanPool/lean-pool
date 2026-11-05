/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.PlaneHilbert
import Mathlib.Tactic.Positivity

/-! The filtered Hilbert polynomial of a principal hypersurface.
Its dimension and multiplicity follow from the exact finite-dimensional
principal-ideal rank identity, without geometric hypotheses. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private lemma principal_binomial_layer_sum (n d N : ℕ) (hN : d ≤ N) :
    (∑ i ∈ range d, (N + n - i).choose n) +
      (N - d + (n + 1)).choose (n + 1) = (N + (n + 1)).choose (n + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hi := ih (by omega)
    have hp := Nat.choose_succ_succ' (N - (d + 1) + (n + 1)) n
    rw [show N - (d + 1) + (n + 1) = N + n - d by omega,
      show N + n - d + 1 = N - d + (n + 1) by omega] at hp
    rw [show N - (d + 1) + (n + 1) = N + n - d by omega]
    omega

/-- Exact filtered Hilbert polynomial of any nonzero principal equation
in n+1 variables, including the constant case. -/
private theorem principal_filteredHilbertPolynomial {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) :
    filteredHilbertPolynomial (Ideal.span {f}) =
      ∑ i ∈ range f.totalDegree, Polynomial.preHilbertPoly ℚ n i := by
  apply filteredHilbertPolynomial_eq_of_eventual
  refine ⟨f.totalDegree, fun N hN => ?_⟩
  have hr := principal_filtered_finrank f hf hN
  rw [finrank_restrictTotalDegree, finrank_restrictTotalDegree] at hr
  simp only [Fintype.card_fin] at hr
  rw [← Nat.choose_symm_add (a := n + 1) (b := N - f.totalDegree),
    ← Nat.choose_symm_add (a := n + 1) (b := N)] at hr
  have hs := principal_binomial_layer_sum n f.totalDegree N hN
  have he : Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) =
      ∑ i ∈ range f.totalDegree, (N + n - i).choose n := by
    rw [Nat.add_comm (n + 1) (N - f.totalDegree), Nat.add_comm (n + 1) N] at hr
    omega
  rw [he, Polynomial.eval_finsetSum, Nat.cast_sum]
  apply sum_congr rfl
  intro i hi
  exact Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (by have := mem_range.mp hi; omega)

private lemma principal_preHilbert_sum_degree_le (n d : ℕ) :
    (∑ i ∈ range d, Polynomial.preHilbertPoly ℚ n i).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_preHilbertPoly ℚ n i).le

private lemma principal_preHilbert_sum_top_coeff (n d : ℕ) :
    (∑ i ∈ range d, Polynomial.preHilbertPoly ℚ n i).coeff n = (d : ℚ) / n.factorial := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_preHilbertPoly_self,
    sum_const, card_range, nsmul_eq_mul, div_eq_mul_inv]

/-- A nonconstant principal equation in n+1 variables has filtered
Hilbert dimension n and multiplicity equal to its total degree. -/
theorem principal_filteredHilbertPolynomial_degree_leadingCoeff
    {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hd : 0 < f.totalDegree) :
    HasAffineDimensionDegree (Ideal.span {f}) n f.totalDegree := by
  have hP := principal_filteredHilbertPolynomial f hf
  have hcoeff := principal_preHilbert_sum_top_coeff n f.totalDegree
  have hn : (∑ i ∈ range f.totalDegree, Polynomial.preHilbertPoly ℚ n i).coeff n ≠ 0 := by
    rw [hcoeff]
    positivity
  have hdegree := le_antisymm (principal_preHilbert_sum_degree_le n f.totalDegree)
    (Polynomial.le_natDegree_of_ne_zero hn)
  exact ⟨by rw [hP, hdegree], by rw [hP, Polynomial.leadingCoeff, hdegree, hcoeff]⟩

/-- The filtered Hilbert polynomial of a nonconstant principal ideal `(f)` in `n + 1` variables has
degree `n`. -/
theorem principal_filteredHilbertPolynomial_natDegree
    {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hd : 0 < f.totalDegree) :
    (filteredHilbertPolynomial (Ideal.span {f})).natDegree = n :=
  (principal_filteredHilbertPolynomial_degree_leadingCoeff f hf hd).natDegree_eq

/-- The filtered Hilbert polynomial of a nonconstant principal ideal `(f)` in `n + 1` variables has
leading coefficient `deg f / n!`, so the hypersurface has degree `deg f`. -/
theorem principal_filteredHilbertPolynomial_leadingCoeff
    {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hd : 0 < f.totalDegree) :
    (filteredHilbertPolynomial (Ideal.span {f})).leadingCoeff =
      (f.totalDegree : ℚ) / n.factorial :=
  (principal_filteredHilbertPolynomial_degree_leadingCoeff f hf hd).leadingCoeff_eq

end
end CCDN
