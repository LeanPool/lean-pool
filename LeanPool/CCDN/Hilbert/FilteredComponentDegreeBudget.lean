/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredPrimeDecomposition
import LeanPool.CCDN.Algebra.BinomialSectionBound
import LeanPool.CCDN.Hilbert.FilteredComponentRank

/-! Additivity of the leading filtered dimension bounds the total degree of
the minimal-prime components of a two-equation section. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A common linear upper bound bounds the sum of the eventual linear
slopes of the minimal-prime components. -/
private theorem minimalPrimeComponents_slope_sum_le {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (C N₀ : ℕ)
    (hupper : ∀ N ≥ N₀, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 1))
    (d : minimalPrimeComponents I → ℕ)
    (hdegree : ∀ P, HasFilteredCurveDegree P.val (d P)) :
    ∑ P, d P ≤ C := by
  classical
  obtain ⟨D, hD⟩ := minimalPrimeComponents_filtered_rank_lower I
  choose Nᵢ cᵢ hNᵢ using hdegree
  let Nmax := Finset.univ.sup Nᵢ
  let c := ∑ P, cᵢ P
  let E := ∑ P, d P
  have hsum (N : ℕ) (hN : Nmax ≤ N) :
      ((∑ P : minimalPrimeComponents I,
          Module.finrank K (filteredCoordinateSpace P.val N) : ℕ) : ℤ) =
        (E : ℤ) * N + c := by
    push_cast
    calc
      _ = ∑ P, ((d P : ℤ) * N + cᵢ P) := by
        apply Finset.sum_congr rfl
        intro P _
        exact hNᵢ P N ((Finset.le_sup (Finset.mem_univ P)).trans hN)
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, E, c, Nat.cast_sum]
  by_contra h
  have hbig : C + 1 ≤ E := by dsimp only [E]; omega
  let N := C * (D + 1) + c.natAbs + Nmax + N₀ + 1
  have hNmax : Nmax ≤ N := by dsimp only [N]; omega
  have hNN₀ : N₀ ≤ D + N := by dsimp only [N]; omega
  have hbound := (hD N).trans (hupper (D + N) hNN₀)
  have hboundZ : (E : ℤ) * N + c ≤ (C : ℤ) * (D + N + 1) := by
    rw [← hsum N hNmax]
    exact_mod_cast hbound
  have hmul : ((C : ℤ) + 1) * N ≤ (E : ℤ) * N := by
    exact_mod_cast Nat.mul_le_mul_right N hbig
  have hc : -(c.natAbs : ℤ) ≤ c := by
    have hh : -c ≤ ((-c).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at hh
    omega
  have hNeq : (N : ℤ) = C * (D + 1) + c.natAbs + Nmax + N₀ + 1 := by
    dsimp only [N]
    push_cast
    rfl
  nlinarith

/-- The product-of-degrees budget holds for the prime components.
Only their eventual Hilbert formulas are inputs to this intermediate lemma. -/
private theorem polynomialSection_minimalPrime_slope_sum_le {K : Type*} [Field K]
    (f g : MvPolynomial (Fin 3) K) (hf : Prime f) (hfg : ¬ f ∣ g)
    (d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ)
    (hdegree : ∀ P, HasFilteredCurveDegree P.val (d P)) :
    ∑ P, d P ≤ f.totalDegree * g.totalDegree := by
  apply minimalPrimeComponents_slope_sum_le (polynomialSectionIdeal f g)
    (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree) _ d hdegree
  intro N hN
  have hh := filteredCoordinateSpace_codim_two_bound (n := 1) hf hfg
    (polynomialSectionIdeal f g) (polynomialSectionIdeal_first_mem f g)
    (polynomialSectionIdeal_second_mem f g) hN
  simpa only [Nat.choose_one_right, Nat.add_comm 1] using hh

/-- The additive degree inequality in the rational curve-degree interface. -/
theorem polynomialSection_minimalPrime_curveDegree_sum_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ)
    (hdegree : ∀ P, HasAffineCurveDegree P.val (d P)) :
    ∑ P, d P ≤ f.totalDegree * g.totalDegree :=
  polynomialSection_minimalPrime_slope_sum_le f g hf.prime hfg d hdegree

end
end CCDN
