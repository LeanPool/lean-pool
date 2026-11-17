/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-!
# Standard monomials of an ideal

For an ideal `I` of `MvPolynomial σ K` and a monomial order `m`, the standard exponents are those
not divisible by the leading exponent of any nonzero element of `I`. A nonzero polynomial
supported on standard exponents never lies in `I`, and division by all nonzero elements of `I`
produces such a representative. For the degree lexicographic order the representative has total
degree at most that of the original polynomial.

## Main definitions

* `Ideal.standardExponents I m`: the exponents not divisible by `m.degree f` for any nonzero
  `f ∈ I`.
* `Ideal.boundedStandardExponents I m N`: the standard exponents of total degree at most `N`.

## Main results

* `Ideal.eq_zero_of_mem_restrictSupport_standardExponents`: a polynomial in `I` supported on
  standard exponents is zero.
* `Ideal.exists_standard_representative_degLex`: every polynomial is congruent modulo `I` to a
  polynomial supported on standard exponents for `degLex`, of no larger total degree.
-/

@[expose] public section

namespace Ideal

open MvPolynomial

variable {K σ : Type*} [Field K]

/-- Exponents not divisible by any leading exponent of a nonzero ideal element. -/
def standardExponents (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) : Set (σ →₀ ℕ) :=
  {a | ∀ f ∈ I, f ≠ 0 → ¬ m.degree f ≤ a}

/-- Standard exponents form a lower set. -/
lemma isLowerSet_standardExponents (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) :
    IsLowerSet (standardExponents I m) := by
  intro a b hab hb f hf hn hfa
  exact hb f hf hn (hfa.trans hab)

/-- A standard polynomial belonging to the ideal is zero. -/
lemma eq_zero_of_mem_restrictSupport_standardExponents
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ)
    {f : MvPolynomial σ K} (hf : f ∈ restrictSupport K (standardExponents I m))
    (hI : f ∈ I) : f = 0 := by
  by_contra hn
  exact (hf (m.degree_mem_support hn)) f hI hn le_rfl

/-- Division with respect to `degLex` gives a standard representative modulo `I` of no larger
total degree. -/
theorem exists_standard_representative_degLex [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K,
      r ∈ restrictSupport K (standardExponents I MonomialOrder.degLex) ∧
      r.totalDegree ≤ f.totalDegree ∧ f - r ∈ I := by
  classical
  let B : Set (MvPolynomial σ K) := {b | b ∈ I ∧ b ≠ 0}
  obtain ⟨g, r, hsum, hdeg, hstd⟩ :=
    MonomialOrder.div_set (m := MonomialOrder.degLex)
      (B := B) (fun b hb => MonomialOrder.isUnit_leadingCoeff.mpr hb.2) f
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a ha b hb hn
    exact hstd a ha b ⟨hb, hn⟩
  · have hg : Finsupp.linearCombination (MvPolynomial σ K)
        (fun b : B => b.val) g ∈ restrictTotalDegree σ K f.totalDegree := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply Submodule.sum_mem
      intro b _
      rw [smul_eq_mul, mul_comm, mem_restrictTotalDegree]
      exact degLex_totalDegree_monotone (hdeg b)
    have hr : r = f - Finsupp.linearCombination (MvPolynomial σ K)
        (fun b : B => b.val) g := by rw [hsum]; ring
    rw [← mem_restrictTotalDegree, hr]
    exact Submodule.sub_mem _ (by rw [mem_restrictTotalDegree]) hg
  · have hg : Finsupp.linearCombination (MvPolynomial σ K)
        (fun b : B => b.val) g ∈ I := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply I.sum_mem
      intro b _
      exact I.mul_mem_left _ b.property.1
    simpa only [hsum, add_sub_cancel_right] using hg

/-- Standard exponents of total degree at most `N`. -/
def boundedStandardExponents (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) :
    Set (σ →₀ ℕ) :=
  {a | a ∈ standardExponents I m ∧ a.degree ≤ N}

end Ideal
