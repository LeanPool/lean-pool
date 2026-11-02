/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialValueBounds
public import LeanPool.NairTenenbaum.Sieve.SmallDivisorMainTerm
public import LeanPool.NairTenenbaum.Sieve.SmallDivisorMajorant

/-! # The small-prefix, large-next-prime contribution

This class contains the first class in §4: a prefix of the irreducible value
factorization has small weighted mass, and its next-prime cutoff exceeds the
sieve bound. No choice of a first crossing prime is built into the class, so
its estimate also applies to any such prefix.
-/

@[expose] public section

namespace NairTenenbaum

/-- A small whole-prime-power prefix with a large cutoff. -/
def PolynomialSystem.HasSmallRoughPrefix {k r : ℕ} (P : PolynomialSystem k r)
    (N : ℕ+) (z : ℝ) (t : ℤ) : Prop :=
  ∃ (n : Tuple r) (q : ℕ), (∀ i, (n i : ℕ) = ((P.R i).eval t).natAbs) ∧
    weightedMass P.exponent (primeSelect n (Finset.range q)) ≤ N ∧ z < (q : ℝ)

/-- The contribution of values admitting a small prefix with a large next-prime cutoff. -/
noncomputable def PolynomialSystem.smallRoughContribution {k r : ℕ} (P : PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (a b : ℤ) (z : ℝ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter (P.HasSmallRoughPrefix N z),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

/-- The first-contribution reduction, with all counting and roughness inputs
proved and only a total-value upper bound remaining as a hypothesis. -/
theorem PolynomialSystem.smallRoughContribution_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (N : ℕ+) (a b : ℤ) {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.smallRoughContribution F N a b (x ^ α) ≤
      A ^ (c / α) * P.smallDivisorSiftedSum F N a b (x ^ α) := by
  classical
  let T := (Finset.Ioc a b).filter (P.HasSmallRoughPrefix N (x ^ α))
  choose! n q hn using fun t (ht : t ∈ T) => (Finset.mem_filter.mp ht).2
  exact P.sum_roughPrefix_le hF hA hB N a b T n q (Finset.filter_subset _ _)
    (fun t ht => (hn t ht).1) hx hα (fun t ht => (hn t ht).2.2)
    (fun t ht => (hn t ht).2.1) (fun t ht => hvalue t (Finset.mem_filter.mp ht).1)

end NairTenenbaum
