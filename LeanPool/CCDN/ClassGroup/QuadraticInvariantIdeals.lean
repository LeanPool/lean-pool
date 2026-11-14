/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import LeanPool.CCDN.ClassGroup.QuadraticNormConjugation
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! Prime ideal orbits in a quadratic number-field extension.
These are the arithmetic inputs for factoring invariant ideals into
extended base ideals and ramified prime factors. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField Ideal
open scoped Pointwise

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [FiniteDimensional F K]

omit [NumberField F] [NumberField K] [FiniteDimensional F K] in
/-- The action of `σ : K ≃ₐ[F] K` on ideals of `𝓞 K` is the image under the induced automorphism of
`𝓞 K`. -/
lemma quadratic_integer_ideal_action (σ : K ≃ₐ[F] K) (I : Ideal (𝓞 K)) :
    σ • I = I.map (RingOfIntegers.mapAlgEquiv σ).toRingHom := by
  rfl

private theorem quadratic_prime_orbit_eq_pair
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] :
    (Q.under (𝓞 F)).primesOver (𝓞 K) = {Q, σ • Q} := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  let : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing _ _ _ F K
  ext P
  constructor
  · intro hP
    have : P.IsPrime := hP.1
    have : P.LiesOver (Q.under (𝓞 F)) := hP.2
    obtain ⟨τ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      (Q.under (𝓞 F)) Q P (K ≃ₐ[F] K)
    rcases quadratic_automorphism_eq_one_or F K hd σ hσ τ with rfl | rfl
    · simp
    · simp
  · intro hP
    rcases Set.mem_insert_iff.mp hP with rfl | hP
    · exact ⟨inferInstance, inferInstance⟩
    · have hP' : P = σ • Q := Set.mem_singleton_iff.mp hP
      subst P
      exact ⟨inferInstance, inferInstance⟩

private theorem quadratic_prime_ramification_identity
    (hd : Module.finrank F K = 2) (Q : Ideal (𝓞 K)) [Q.IsPrime] :
    ((Q.under (𝓞 F)).primesOver (𝓞 K)).ncard *
      (Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F)) = 2 := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  let : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing _ _ _ F K
  have hh := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Q.under (𝓞 F)) (𝓞 K) (K ≃ₐ[F] K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q (K ≃ₐ[F] K),
    Ideal.inertiaDegIn_eq_inertiaDeg (Q.under (𝓞 F)) Q (K ≃ₐ[F] K),
    IsGalois.card_aut_eq_finrank, hd] at hh
  exact hh

/-- In a quadratic extension `K / F`, every prime ideal of `𝓞 K` has ramification index `1` or `2`
over `𝓞 F`. -/
theorem quadratic_prime_ramification_one_or_two
    (hd : Module.finrank F K = 2) (Q : Ideal (𝓞 K)) [Q.IsPrime] :
    Q.ramificationIdx (𝓞 F) = 1 ∨ Q.ramificationIdx (𝓞 F) = 2 := by
  have hh := quadratic_prime_ramification_identity F K hd Q
  have hdvd : Q.ramificationIdx (𝓞 F) ∣ 2 := by
    refine ⟨((Q.under (𝓞 F)).primesOver (𝓞 K)).ncard * Q.inertiaDeg (𝓞 F), ?_⟩
    nlinarith only [hh]
  exact (Nat.dvd_prime Nat.prime_two).mp hdvd

/-- In a quadratic extension with nontrivial automorphism `σ`, a prime ideal of `𝓞 K` not fixed by
`σ` is unramified over `𝓞 F`. -/
theorem quadratic_moving_prime_unramified
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hmove : σ • Q ≠ Q) :
    Q.ramificationIdx (𝓞 F) = 1 := by
  have hh := quadratic_prime_ramification_identity F K hd Q
  rw [quadratic_prime_orbit_eq_pair F K hd σ hσ Q] at hh
  have hcard : ({Q, σ • Q} : Set (Ideal (𝓞 K))).ncard = 2 := by
    simp [hmove.symm]
  rw [hcard] at hh
  have he := Q.ramificationIdx_pos (𝓞 F)
  have hf := Q.inertiaDeg_pos (𝓞 F)
  nlinarith

/-- In a quadratic extension with nontrivial automorphism `σ`, a nonzero prime `Q` of `𝓞 K` fixed by
`σ` is the only prime above its contraction `P`, so `P 𝓞 K = Q ^ e` with `e` its ramification
index. -/
theorem quadratic_fixed_prime_extension
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) (hfix : σ • Q = Q) :
    (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) =
      Q ^ Q.ramificationIdx (𝓞 F) := by
  have hp : Q.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hQ
  have : (Q.under (𝓞 F)).IsMaximal := (inferInstance : (Q.under (𝓞 F)).IsPrime).isMaximal hp
  have hset : ((Q.under (𝓞 F)).primesOver (𝓞 K)).toFinset = {Q} := by
    ext P
    simp [quadratic_prime_orbit_eq_pair F K hd σ hσ Q, hfix]
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp, hset]
  simp

/-- In a quadratic extension with nontrivial automorphism `σ`, a nonzero prime `Q` of `𝓞 K` not
fixed by `σ` satisfies `P 𝓞 K = Q * σ Q`, where `P` is its contraction to `𝓞 F`. -/
theorem quadratic_moving_prime_extension
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) (hmove : σ • Q ≠ Q) :
    (Q.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) = Q * (σ • Q) := by
  let : Algebra.IsQuadraticExtension F K := ⟨hd⟩
  let : IsGaloisGroup (K ≃ₐ[F] K) (𝓞 F) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing _ _ _ F K
  have hp : Q.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hQ
  have : (Q.under (𝓞 F)).IsMaximal := (inferInstance : (Q.under (𝓞 F)).IsPrime).isMaximal hp
  have he := quadratic_moving_prime_unramified F K hd σ hσ Q hmove
  have he' : (σ • Q).ramificationIdx (𝓞 F) = 1 := by
    rw [Ideal.ramificationIdx_smul, he]
  have hset : ((Q.under (𝓞 F)).primesOver (𝓞 K)).toFinset = {Q, σ • Q} := by
    ext P
    simp [quadratic_prime_orbit_eq_pair F K hd σ hσ Q]
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp, hset]
  simp [hmove.symm, he, he']

end
end CCDN
