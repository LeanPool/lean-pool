/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Localization.FractionRing
import LeanPool.CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! Nonconstant prime polynomials remain prime when coefficients are localized.
This also proves preservation of irreducibility under purely transcendental
coefficient extension, using a swap of the two polynomial variable families. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A nonconstant polynomial over a domain cannot divide a nonzero constant. -/
private theorem mvPolynomial_not_dvd_nonzero_constant
    {R σ : Type*} [CommRing R] [IsDomain R]
    (f : MvPolynomial σ R) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    (a : R) (ha : a ≠ 0) : ¬ f ∣ C a := by
  rintro ⟨g, hg⟩
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, mul_zero] at hg
    exact ha ((C_injective σ R) (by simpa using hg))
  have hdeg := totalDegree_mul_of_isDomain hf hg0
  rw [← hg, totalDegree_C] at hdeg
  omega

/-- Prime polynomials of positive variable degree survive coefficient
localization at nonzero elements. -/
theorem prime_mvPolynomial_map_localization
    {R S σ : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R)
    (f : MvPolynomial σ R) (hf : Prime f) (hd : 0 < f.totalDegree) :
    Prime (MvPolynomial.map (algebraMap R S) f) := by
  let N : Submonoid (MvPolynomial σ R) := M.map C
  let I : Ideal (MvPolynomial σ R) := Ideal.span {f}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf
  have hdis : Disjoint (N : Set (MvPolynomial σ R)) (I : Set (MvPolynomial σ R)) := by
    rw [Set.disjoint_left]
    intro q hq hqi
    obtain ⟨a, ha, rfl⟩ := hq
    exact mvPolynomial_not_dvd_nonzero_constant f hf.ne_zero hd a
      (mem_nonZeroDivisors_iff_ne_zero.mp (hM ha)) (Ideal.mem_span_singleton.mp hqi)
  have hp := IsLocalization.isPrime_of_isPrime_disjoint N (MvPolynomial σ S) I hI hdis
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have hne : MvPolynomial.map (algebraMap R S) f ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective _ hinj)).mpr hf.ne_zero
  apply (Ideal.span_singleton_prime hne).mp
  simpa only [I, Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] using hp

/-- Irreducibility survives adjoining algebraically independent parameters
and then passing to their rational function field. -/
theorem irreducible_mvPolynomial_map_fraction_parameters
    {K F σ τ : Type*} [Field K] [Field F]
    [Algebra (MvPolynomial τ K) F] [IsFractionRing (MvPolynomial τ K) F]
    (f : MvPolynomial σ K) (hf : Irreducible f) (hd : 0 < f.totalDegree) :
    Irreducible (MvPolynomial.map ((algebraMap (MvPolynomial τ K) F).comp C) f) := by
  let g : MvPolynomial σ (MvPolynomial τ K) := MvPolynomial.map C f
  have hg : Prime g := by
    have hC : Prime (C f : MvPolynomial τ (MvPolynomial σ K)) :=
      (MvPolynomial.prime_C_iff τ).mpr hf.prime
    have h := (MulEquiv.prime_iff (MvPolynomial.commAlgEquiv K τ σ)).mpr hC
    simpa only [MvPolynomial.commAlgEquiv_C, g] using h
  have hdeg : 0 < g.totalDegree := by
    have he : g.totalDegree = f.totalDegree := totalDegree_map_of_injective (C_injective τ K) _
    rw [he]
    exact hd
  have h := prime_mvPolynomial_map_localization (S := F)
    (nonZeroDivisors (MvPolynomial τ K)) le_rfl g hg hdeg
  simpa only [g, MvPolynomial.map_map] using h.irreducible

end
end CCDN
