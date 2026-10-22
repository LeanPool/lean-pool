/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.QuadraticAmbiguousClassBound
public import LeanPool.CCDN.ClassGroup.QuadraticInvariantFactorization
import LeanPool.CCDN.ClassGroup.DiscriminantPrimeIdealCover
import LeanPool.CCDN.ClassGroup.InvariantIdealIntegralRepresentative
import LeanPool.CCDN.ClassGroup.QuadraticInvariantIdeals
import LeanPool.CCDN.ClassGroup.QuadraticNormConjugation
import LeanPool.CCDN.ForMathlib.FiniteGroupPowerTorsion

/-!
The two-torsion in the strongly ambiguous class group is
bounded by base-field two-torsion and the finite set of ramified primes.
The cover comes from the proved invariant-ideal factorization.

Ideal-class notation for finite products of nonzero integral ideals.
The value at the zero ideal is set to one only to make the indexing
function total; multiplicativity below explicitly requires nonzero ideals.
-/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The ideal class of an integral ideal, with the zero ideal sent to the trivial class. -/
def integralIdealClass (I : Ideal R) : ClassGroup R :=
  if h : I = 0 then 1 else ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h⟩

private lemma integralIdealClass_eq (I : Ideal R) (hI : I ≠ 0) :
    integralIdealClass I = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ := by
  simp only [integralIdealClass, dite_eq_right hI]

/-- The unit ideal has trivial ideal class. -/
lemma integralIdealClass_one : integralIdealClass (1 : Ideal R) = 1 := by
  rw [integralIdealClass_eq _ one_ne_zero]
  exact map_one ClassGroup.mk0

/-- The top ideal has trivial ideal class. -/
@[simp] lemma integralIdealClass_top : integralIdealClass (⊤ : Ideal R) = 1 := by
  simpa only [Ideal.one_eq_top] using (integralIdealClass_one (R := R))

private lemma integralIdealClass_mk0 (I : (Ideal R)⁰) :
    integralIdealClass (I : Ideal R) = ClassGroup.mk0 I := by
  exact integralIdealClass_eq _ (mem_nonZeroDivisors_iff_ne_zero.mp I.property)

private lemma integralIdealClass_mul {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    integralIdealClass (I * J) = integralIdealClass I * integralIdealClass J := by
  rw [integralIdealClass_eq _ (mul_ne_zero hI hJ),
    integralIdealClass_eq _ hI, integralIdealClass_eq _ hJ]
  exact map_mul (ClassGroup.mk0 (R := R))
    (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ : (Ideal R)⁰)
    (⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩ : (Ideal R)⁰)

private lemma integralIdealClass_prod (s : Finset (Ideal R)) (hs : ∀ I ∈ s, I ≠ 0) :
    integralIdealClass (∏ I ∈ s, I) = ∏ I ∈ s, integralIdealClass I := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (integralIdealClass_one (R := R))
  | @insert I s hIs ih =>
    have hI := hs I (Finset.mem_insert_self I s)
    have hs' : ∀ J ∈ s, J ≠ 0 := fun J hJ ↦ hs J (Finset.mem_insert_of_mem hJ)
    rw [Finset.prod_insert hIs, integralIdealClass_mul hI (Finset.prod_ne_zero_iff.mpr hs'),
      ih hs', Finset.prod_insert hIs]

private lemma integralIdealClass_extension
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [Module.IsTorsionFree R S] (I : Ideal R) (hI : I ≠ 0) :
    integralIdealClass (I.map (algebraMap R S)) =
      ClassGroup.extendedHom R S (integralIdealClass I) := by
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  rw [integralIdealClass_eq _ hI, ClassGroup.extendedHom_mk0]
  exact integralIdealClass_mk0 (ClassGroup.extendedIdeal R S I₀)

end
end CCDN

namespace CCDN
noncomputable section
open NumberField
open scoped Pointwise nonZeroDivisors

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

private theorem stronglyAmbiguousClassGroup_ramified_cover
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ Q, IsQuadraticRamifiedPrime F K Q → Q ∈ S)
    (c : stronglyAmbiguousClassGroup F K σ) :
    ∃ a : ClassGroup (𝓞 F), ∃ t : S.powerset,
      c.val = ClassGroup.extendedHom (𝓞 F) (𝓞 K) a *
        ∏ Q ∈ t.val, integralIdealClass Q := by
  obtain ⟨J, hJ, hJc⟩ := (mem_stronglyAmbiguousClassGroup F K σ c.val).mp c.property
  have hσO : Function.Involutive (RingOfIntegers.mapAlgEquiv σ).toRingEquiv := by
    intro x
    apply RingOfIntegers.ext
    exact quadratic_automorphism_involutive F K hd σ (x : K)
  obtain ⟨I, hIinv, hIc⟩ :=
    exists_invariant_integral_ideal_representative
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv hσO J hJ
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hIinv' : σ • (I : Ideal (𝓞 K)) = I := by
    rw [quadratic_integer_ideal_action]
    exact hIinv
  have hc : integralIdealClass (I : Ideal (𝓞 K)) = c.val :=
    (integralIdealClass_mk0 I).trans (hIc.trans hJc)
  obtain ⟨A, t, hA, ht, hfact⟩ :=
    invariant_integral_ideal_ramified_factorization F K hd σ hσ I hI0 hIinv'
  have htS : t ⊆ S := fun Q hQ ↦ hS Q (ht Q hQ)
  have ht0 : ∀ Q ∈ t, Q ≠ 0 := fun Q hQ ↦ (ht Q hQ).2.1
  have hmap0 : A.map (algebraMap (𝓞 F) (𝓞 K)) ≠ 0 :=
    Ideal.map_ne_bot_of_ne_bot hA
  refine ⟨integralIdealClass A, ⟨t, Finset.mem_powerset.mpr htS⟩, ?_⟩
  rw [← hc, hfact, integralIdealClass_mul hmap0 (Finset.prod_ne_zero_iff.mpr ht0),
    integralIdealClass_extension (𝓞 K) A hA, integralIdealClass_prod t ht0]

private theorem stronglyAmbiguousTwoTorsion_card_le_ramified_cover
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ Q, IsQuadraticRamifiedPrime F K Q → Q ∈ S) :
    Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F * 2 ^ S.card := by
  have hh := MonoidHom.card_powMonoidHom_ker_le_of_coset_cover
    (ClassGroup.extendedHom (𝓞 F) (𝓞 K)) (stronglyAmbiguousClassGroup F K σ)
    (fun t : S.powerset ↦ ∏ Q ∈ t.val, integralIdealClass Q)
    (stronglyAmbiguousClassGroup_ramified_cover F K hd σ hσ S hS) 2
  simpa only [Fintype.card_coe, Finset.card_powerset, stronglyAmbiguousTwoTorsion,
    classGroupTwoTorsionCard, classGroupTwoTorsion] using hh

/-- A fully constructed discriminant-prime cover gives the
strongly ambiguous two-torsion estimate. -/
theorem stronglyAmbiguousTwoTorsion_card_le_discriminant_primes
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1) :
    Nat.card (stronglyAmbiguousTwoTorsion F K σ) ≤
      classGroupTwoTorsionCard F *
        2 ^ (Module.finrank ℚ K * (NumberField.discr K).natAbs.primeFactors.card) := by
  have hh := stronglyAmbiguousTwoTorsion_card_le_ramified_cover F K hd σ hσ
    (discriminantPrimeIdealCover K) (by
      intro Q hQ
      have : Q.IsPrime := hQ.1
      exact mem_discriminantPrimeIdealCover_of_ramification_two K F Q hQ.2.1 hQ.2.2)
  exact hh.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by omega) (discriminantPrimeIdealCover_card_le K)))

end
end CCDN
