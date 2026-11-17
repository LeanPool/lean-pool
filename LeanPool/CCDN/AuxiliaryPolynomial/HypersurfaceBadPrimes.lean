/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadReduction
public import LeanPool.CCDN.Plane.FiniteFieldConstants
import LeanPool.CCDN.AuxiliaryPolynomial.UniversalPlaneBadReduction

/-! The finite set of bad primes of an integer hypersurface. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A polynomial with an irreducible image under a coefficient map is nonzero. -/
lemma ne_zero_of_irreducible_map {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    {φ : R →+* S} {f : MvPolynomial σ R} (h : Irreducible (map φ f)) : f ≠ 0 := by
  rintro rfl
  exact h.ne_zero (map_zero _)

/-- Good reduction at a prime `p`: the reduction of `f` modulo `p` is nonzero and
absolutely irreducible. -/
abbrev HasGoodReduction {σ : Type*} (f : MvPolynomial σ ℤ) (p : ℕ) [Fact p.Prime] : Prop :=
  map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
    Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f))

/-- A positive integer and the exact finite bad-prime set above the
degree. -/
private theorem exists_hypersurface_bad_prime_set
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Finite σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    ∃ (D : ℤ) (B : Finset ℕ), 0 < D ∧
      (∀ p, p ∈ B ↔ f.totalDegree < p ∧ HypersurfaceBadReduction f p) ∧
      (∀ p ∈ B, (p : ℤ) ∣ D) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨rows, cols, e, he, hdiv⟩ := exists_integer_hypersurface_bad_prime_witness f hf hpos
  let D := |(universalPlaneBadWitness f rows cols).coeff e|
  have hD : 0 < D := abs_pos.mpr he
  have hdiv' (p : ℕ) (hp : f.totalDegree < p) (hbad : HypersurfaceBadReduction f p) :
      (p : ℤ) ∣ D := by
    obtain ⟨hpp, hbad⟩ := hbad
    let : Fact p.Prime := ⟨hpp⟩
    exact (dvd_abs _ _).mpr (hdiv p hp hbad)
  let B := D.natAbs.primeFactors.filter (fun p => f.totalDegree < p ∧ HypersurfaceBadReduction f p)
  have hmem (p : ℕ) : p ∈ B ↔ f.totalDegree < p ∧ HypersurfaceBadReduction f p := by
    constructor
    · exact fun h => (Finset.mem_filter.mp h).2
    · intro hp
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_primeFactors.mpr ⟨hp.2.choose, ?_, Int.natAbs_ne_zero.mpr hD.ne'⟩, hp⟩
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (hdiv' p hp.1 hp.2)
  exact ⟨D, B, hD, hmem, fun p hp => hdiv' p ((hmem p).mp hp).1 ((hmem p).mp hp).2⟩

/-- Finiteness of the paper's bad-prime set above 27*d^4. A stronger set above
d is finite; filtering it gives the exact prescribed cutoff. -/
theorem finite_hypersurface_bad_primes
    {L σ : Type*} [Field L] [CharZero L] [IsAlgClosed L] [Finite σ]
    (f : MvPolynomial (Option σ) ℤ)
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) :
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p}.Finite := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨_, B, _, hmem, _⟩ := exists_hypersurface_bad_prime_set f hf hpos
  apply B.finite_toSet.subset
  intro p hp
  apply (hmem p).mpr
  refine ⟨?_, hp.2⟩
  have h1 := Nat.le_mul_self f.totalDegree
  have h2 := Nat.le_mul_self (f.totalDegree * f.totalDegree)
  have h3 : 27 * f.totalDegree ^ 4 < p := hp.1
  nlinarith [h3]

end
end CCDN
