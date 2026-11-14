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
import LeanPool.CCDN.Algebra.BinomialSectionBound
import LeanPool.CCDN.Algebra.CoordinatePowerGeneration
import LeanPool.CCDN.Hilbert.FilteredComponentDegreeBudget
import LeanPool.CCDN.Hilbert.FilteredHilbertLinearity
import LeanPool.CCDN.Hilbert.PrimeComponentTranscendence

/-!
A finite decomposition of a proper affine surface section into
rational prime curves, with a proved additive degree budget. Components with
no rational points are discarded before requiring positive curve degrees.

An eventual linear upper bound gives an eventual linear Hilbert
formula, with its slope bounded by the original coefficient.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem filteredCoordinateSpace_eventually_linear_of_eventual_bound
    {K σ : Type*} [Field K] [Finite σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (C T : ℕ)
    (hbound : ∀ N ≥ T, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2)) :
    ∃ d ≤ C, HasFilteredCurveDegree I d := by
  classical
  let := Fintype.ofFinite σ
  have hglobal (N : ℕ) (_hN : 14 ≤ N) :
      Module.finrank K (filteredCoordinateSpace I N) ≤ (C * (T + 2)) * (N + 2) := by
    by_cases hTN : T ≤ N
    · apply (hbound N hTN).trans
      exact Nat.mul_le_mul_right (N + 2) (Nat.le_mul_of_pos_right C (by omega))
    · have hNT : N ≤ T := by omega
      have hh := Submodule.finrank_mono (filteredCoordinateSpace_mono I hNT)
      exact (hh.trans (hbound T le_rfl)).trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨d, _, N, c, hlinear⟩ := filteredCoordinateSpace_eventually_linear I (C * (T + 2)) hglobal
  refine ⟨d, ?_, N, c, hlinear⟩
  apply eventual_linear_slope_le
    (fun k => Module.finrank K (filteredCoordinateSpace I (k + T)))
    (fun k => C * (k + T + 2)) d C
  · refine ⟨N, c + (d : ℤ) * T, ?_⟩
    intro k hk
    rw [hlinear (k + T) (by omega)]
    push_cast
    ring
  · refine ⟨0, (C : ℤ) * (T + 2), ?_⟩
    intro k _
    push_cast
    ring
  · intro k
    exact hbound (k + T) (by omega)

/-- A proper intersection of two equations in affine three-space has an
eventually linear Hilbert function with slope at most the product of degrees.
This holds for every ideal containing the equations, not just prime ideals. -/
private theorem proper_intersection_eventual_linear_degree {K : Type*} [Field K]
    {f g : MvPolynomial (Fin 3) K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial (Fin 3) K)) (hIf : f ∈ I) (hIg : g ∈ I) :
    ∃ d ≤ f.totalDegree * g.totalDegree, HasFilteredCurveDegree I d := by
  apply filteredCoordinateSpace_eventually_linear_of_eventual_bound I
    (f.totalDegree * g.totalDegree) (f.totalDegree + g.totalDegree)
  intro N hN
  have hh := filteredCoordinateSpace_codim_two_bound hf hfg I hIf hIg hN
  simp only [Nat.choose_one_right] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (by omega))

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Every minimal-prime component has an eventual affine Hilbert
degree. The slope is allowed to be zero until a rational point is exhibited. -/
theorem polynomialSection_minimalPrime_degrees_exist
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    ∃ d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ,
      (∀ P, HasAffineCurveDegree P.val (d P)) ∧
        ∑ P, d P ≤ f.totalDegree * g.totalDegree := by
  classical
  have hex (P : minimalPrimeComponents (polynomialSectionIdeal f g)) :
      ∃ d : ℕ, HasAffineCurveDegree P.val d := by
    obtain ⟨d, _, h⟩ := proper_intersection_eventual_linear_degree hf.prime hfg P.val
      (le_minimalPrimeComponents P.property (polynomialSectionIdeal_first_mem f g))
      (le_minimalPrimeComponents P.property (polynomialSectionIdeal_second_mem f g))
    exact ⟨d, h⟩
  choose d hd using hex
  exact ⟨d, hd, polynomialSection_minimalPrime_curveDegree_sum_le f g hf hfg d hd⟩

/-- A proper section in affine three-space is covered exactly by a finite
set of rational prime curves. Their positive Hilbert degrees sum to
at most the product of the two equation degrees. All components and degrees
are constructed, including the case of an empty common zero set. -/
theorem exists_completeIntersection_curve_components
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ d : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ P ∈ S, IsSectionCurve f g P (d P)) ∧
        zeroLocus f ∩ zeroLocus g = ⋃ P ∈ S, idealZeroLocus P ∧
        (∑ P ∈ S, d P) ≤ f.totalDegree * g.totalDegree ∧
        (∀ P ∈ S, (polynomialSectionIdeal f g).IsMinimalPrime P) := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  obtain ⟨δ, hδ, hsumδ⟩ := polynomialSection_minimalPrime_degrees_exist f g hf hfg
  let d (P : Ideal (CoordinatePolynomial 3)) := if hP : P ∈ T then δ ⟨P, hP⟩ else 0
  let S := T.filter (fun P => (idealZeroLocus P).Nonempty)
  have hd (P : T) : d P.val = δ P := by
    simp only [d, dite_eq_left P.property]
    rfl
  have hTP (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      (polynomialSectionIdeal f g).IsMinimalPrime P := mem_minimalPrimeComponents.mp hP
  have hcurve (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      HasAffineCurveDegree P (d P) := by
    rw [hd ⟨P, hP⟩]
    exact hδ ⟨P, hP⟩
  refine ⟨S, d, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨hPT, z, hz⟩ := Finset.mem_filter.mp hP
    have hminimal := hTP P hPT
    have : P.IsPrime := hminimal.isPrime
    have hheight : P.height = 2 :=
      Ideal.height_eq_two_of_mem_minimalPrimes_span_pair hf.prime hfg hminimal
    have hdeg := hcurve P hPT
    exact ⟨⟨hminimal.isPrime, hheight, hminimal.le (polynomialSectionIdeal_first_mem f g), hdeg⟩,
      hminimal.le (polynomialSectionIdeal_second_mem f g),
      height_two_eventual_slope_pos_of_point P hheight z hz hdeg⟩
  · ext x
    constructor
    · intro hx
      have hxi : x ∈ idealZeroLocus (polynomialSectionIdeal f g) := by
        rw [idealZeroLocus_polynomialSectionIdeal]
        exact hx
      rw [idealZeroLocus_eq_union_minimalPrimeComponents] at hxi
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxi
      obtain ⟨hPT, hxP⟩ := Set.mem_iUnion.mp hxP
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hPT, ⟨x, hxP⟩⟩, hxP⟩⟩
    · intro hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hxP
      have hminimal := hTP P (Finset.mem_filter.mp hPS).1
      exact ⟨hxP f (hminimal.le (polynomialSectionIdeal_first_mem f g)),
        hxP g (hminimal.le (polynomialSectionIdeal_second_mem f g))⟩
  · have hsumT : (∑ P ∈ T, d P) = ∑ P, δ P := by
      rw [← Finset.sum_coe_sort T d]
      exact Finset.sum_congr rfl (fun P _ => hd P)
    calc
      _ ≤ ∑ P ∈ T, d P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
      _ = _ := hsumT
      _ ≤ _ := hsumδ
  · intro P hPS
    exact hTP P (Finset.mem_filter.mp hPS).1

end
end CCDN
