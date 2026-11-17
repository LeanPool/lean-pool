/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredPrimeDecomposition
public import LeanPool.CCDN.Surface.CurveComponents
import LeanPool.CCDN.ForMathlib.KrullHeight
import LeanPool.CCDN.Plane.Bezout
import LeanPool.CCDN.Surface.CompleteIntersectionDegreeBudget
import LeanPool.CCDN.Surface.NonlinearCount

/-! Degree and proper-section budgets for any finite family of distinct
prime curves on a surface section. A curve constructed by another
auxiliary is counted as a component of the section whenever its ideal
contains the section's equation. -/

@[expose] public section
namespace CCDN
noncomputable section

private theorem height_two_prime_isMinimalPrime_section
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (P : Ideal (CoordinatePolynomial 3)) (hP : P.IsPrime) (hheight : P.height = 2)
    (hfP : f ∈ P) (hgP : g ∈ P) :
    (polynomialSectionIdeal f g).IsMinimalPrime P := by
  have : P.IsPrime := hP
  have hle : polynomialSectionIdeal f g ≤ P := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hfP
    · have hxg : x = g := Set.mem_singleton_iff.mp hx
      subst x
      exact hgP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  have : Q.IsPrime := hQ.isPrime
  have hQheight : Q.height = 2 := Ideal.height_eq_two_of_mem_minimalPrimes_span_pair hf.prime hfg hQ
  have hQP' : Q = P := by
    by_contra hne
    have hh := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne)
    rw [hQheight, hheight] at hh
    norm_num at hh
  subst Q
  exact hQ

/-- Distinct prime curves of height two contained in a proper surface
section have total degree at most the product of the equation degrees. -/
theorem surface_prime_curve_degree_sum_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ P ∈ S, IsSurfaceCurve f P (δ P) ∧ g ∈ P) :
    ∑ P ∈ S, δ P ≤ f.totalDegree * g.totalDegree := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  obtain ⟨d, hd, hsum⟩ := polynomialSection_minimalPrime_degrees_exist f g hf hfg
  let e (P : Ideal (CoordinatePolynomial 3)) := if hP : P ∈ T then d ⟨P, hP⟩ else 0
  have hST : S ⊆ T := by
    intro P hPS
    obtain ⟨⟨hP, hheight, hfP, _⟩, hgP⟩ := hS P hPS
    exact mem_minimalPrimeComponents.mpr
      (height_two_prime_isMinimalPrime_section f g hf hfg P hP hheight hfP hgP)
  have he (P : T) : e P.val = d P := by
    simp only [e, dite_eq_left P.property]
    rfl
  have heq (P) (hPS : P ∈ S) : δ P = e P := by
    rw [he ⟨P, hST hPS⟩]
    exact affineCurveDegree_unique (hS P hPS).1.degree (hd ⟨P, hST hPS⟩)
  calc
    _ = ∑ P ∈ S, e P := Finset.sum_congr rfl heq
    _ ≤ ∑ P ∈ T, e P :=
      Finset.sum_le_sum_of_subset_of_nonneg hST (by intros; omega)
    _ = ∑ P, d P := by
      rw [← Finset.sum_coe_sort T e]
      exact Finset.sum_congr rfl (fun P _ => he P)
    _ ≤ _ := hsum

open Classical in
/-- For curves `P ∈ S` on the irreducible surface `f = 0` whose ideals contain `g` (with `f`
not dividing `g`), the integral points of height at most `B` on `h = 0` lying on those curves
whose ideals do not contain `h` number at most `deg f * deg g * deg h`. -/
theorem surface_curve_crossing_count_le
    (f g h : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (δ : Ideal (CoordinatePolynomial 3) → ℕ)
    (hS : ∀ P ∈ S, IsSurfaceCurve f P (δ P) ∧ g ∈ P) (B : ℝ) :
    count (⋃ P ∈ S.filter (fun P => h ∉ P), idealZeroLocus P ∩ zeroLocus h) B ≤
      f.totalDegree * g.totalDegree * h.totalDegree := by
  classical
  let T := S.filter (fun P => h ∉ P)
  have hcurve (P) (hPT : P ∈ T) :
      count (idealZeroLocus P ∩ zeroLocus h) B ≤ δ P * h.totalDegree := by
    obtain ⟨hPS, hhP⟩ := Finset.mem_filter.mp hPT
    have : P.IsPrime := (hS P hPS).1.isPrime
    exact count_curve_section_le P (hS P hPS).1.degree h hhP B
  have hbudget := surface_prime_curve_degree_sum_le f g hf hfg T δ
    (fun P hP => hS P (Finset.mem_filter.mp hP).1)
  calc
    _ ≤ ∑ P ∈ T, count (idealZeroLocus P ∩ zeroLocus h) B :=
      count_biUnion_finset_le T _ B
    _ ≤ ∑ P ∈ T, δ P * h.totalDegree := Finset.sum_le_sum hcurve
    _ = (∑ P ∈ T, δ P) * h.totalDegree := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hbudget

end
end CCDN
