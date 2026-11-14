/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.MonomialOrthants
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import LeanPool.CCDN.Hilbert.OrthantMultiplicity

/-! Maximal standard-monomial orthants construct algebraically
independent original coordinates of cardinality equal to Hilbert dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma algebraicIndependent_coordinates_of_standard
    {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ)
    (j : ι → σ) (hj : Function.Injective j)
    (hstd : ∀ a : ι →₀ ℕ, a.mapDomain j ∈ Ideal.standardExponents I m) :
    AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (X (j i))) := by
  classical
  apply algebraicIndependent_iff.mpr
  intro p hp
  have he : aeval (fun i => (Ideal.Quotient.mk I) (X (j i))) =
      (Ideal.Quotient.mkₐ K I).comp (rename j) := by
    ext i
    simp
  rw [he] at hp
  have hmem : rename j p ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hp
  have hs : rename j p ∈ restrictSupport K (Ideal.standardExponents I m) := by
    intro a ha
    change a ∈ (rename j p).support at ha
    rw [support_rename_of_injective hj] at ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact hstd b
  have hz := Ideal.eq_zero_of_mem_restrictSupport_standardExponents I m hs hmem
  exact (rename_injective j hj) (by simpa only [map_zero] using hz)

private lemma orthant_free_monomials_standard {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (B : ℕ)
    (hstable : ∀ a, a ∈ standardExponentVectors I m ↔
      clampExponent B a ∈ standardExponentVectors I m)
    (b : σ → Fin (B + 1))
    (hb : (fun i => (b i).val) ∈ standardExponentVectors I m)
    (t : orthantFree b →₀ ℕ) :
    t.mapDomain Subtype.val ∈ Ideal.standardExponents I m := by
  have he : orthantExpand b t ∈ standardExponentVectors I m := by
    apply (hstable _).mpr
    rw [clamp_orthantExpand]
    exact hb
  apply Ideal.isLowerSet_standardExponents I m (a := Finsupp.equivFunOnFinite.symm
    (orthantExpand b t)) _ he
  intro i
  change (t.mapDomain Subtype.val) i ≤ orthantExpand b t i
  by_cases hi : (b i).val = B
  · have hh := Finsupp.mapDomain_apply_of_injective
      (Subtype.val_injective : Function.Injective (fun i : orthantFree b => i.val))
      t ⟨i, hi⟩
    rw [hh]
    simp [orthantExpand, hi]
  · rw [Finsupp.mapDomain_of_notMem_range]
    · exact Nat.zero_le _
    · rintro ⟨j, rfl⟩
      exact hi j.property

/-- The independent coordinates are constructed from a maximal
standard orthant, with exactly the degree of the Hilbert polynomial. -/
theorem exists_hilbert_dimension_independent_coordinates
    {K σ : Type*} [Field K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    ∃ U : Set σ, Nat.card U = (filteredHilbertPolynomial I).natDegree ∧
      AlgebraicIndependent K (fun i : U => (Ideal.Quotient.mk I) (X i.val)) := by
  classical
  let S := standardExponentVectors I MonomialOrder.degLex
  obtain ⟨B, _, hB⟩ := lowerSet_clamp_stabilizes S
    (standardExponentVectors_lower I MonomialOrder.degLex)
  let s := lowerSetOrthantPatterns S B
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := standardExponentVectors_nonempty I hI
    refine ⟨exponentPattern B a, ?_⟩
    simp only [s, lowerSetOrthantPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hB a).mp ha
  have hpoly : filteredHilbertPolynomial I = lowerSetOrthantPolynomial S B := by
    apply filteredHilbertPolynomial_eq_of_eventual
    refine ⟨Fintype.card σ * B, fun n hn => ?_⟩
    rw [lowerSetOrthantPolynomial_eval S B hB n hn,
      filteredCoordinateSpace_finrank_eq_vector_card]
  obtain ⟨_, hdeg, _⟩ := sum_preHilbertPoly_leading s hs
    (fun b => Fintype.card (orthantFree b)) orthantBaseDegree
  obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_sup s hs
    (fun b => Fintype.card (orthantFree b))
  refine ⟨{i | (b i).val = B}, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, hpoly, lowerSetOrthantPolynomial_eq_sum, hdeg, he]
    exact Fintype.card_congr (Equiv.refl _)
  · exact algebraicIndependent_coordinates_of_standard I MonomialOrder.degLex
      Subtype.val Subtype.val_injective
      (orthant_free_monomials_standard I MonomialOrder.degLex B hB b
        (Finset.mem_filter.mp hb).2)

end
end CCDN
