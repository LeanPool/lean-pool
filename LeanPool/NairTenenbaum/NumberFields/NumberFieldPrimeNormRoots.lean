/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.IdealNormDirichlet
public import LeanPool.NairTenenbaum.NumberFields.NumberFieldResidueRoots

/-! # Prime-norm ideals and residue roots

At primes coprime to the conductor exponent, residue roots account for
all ideals of prime norm, not merely a subset of them.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial NumberField Ideal KummerDedekind

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem conductor_exponent_mem (θ : 𝓞 K) :
    (RingOfIntegers.exponent θ : 𝓞 K) ∈ conductor ℤ θ := by
  have H := Int.ideal_span_absNorm_eq_self ((conductor ℤ θ).comap (algebraMap ℤ (𝓞 K)))
  have HM : (RingOfIntegers.exponent θ : ℤ) ∈
      (conductor ℤ θ).comap (algebraMap ℤ (𝓞 K)) := by
    rw [← H]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [Ideal.mem_comap, map_natCast] using HM

omit [NumberField K] in
theorem zmod_hom_ext_generator (θ : 𝓞 K) {p : ℕ} (hp : p.Prime)
    (hc : p.Coprime (RingOfIntegers.exponent θ)) {f g : 𝓞 K →+* ZMod p}
    (hθ : f θ = g θ) : f = g := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : (RingOfIntegers.exponent θ : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hc
  apply RingHom.ext
  intro x
  obtain ⟨Q, hQ⟩ := Algebra.adjoin_mem_exists_aeval ℤ θ
    (mem_conductor_iff.mp (conductor_exponent_mem θ) x)
  have H : f ((RingOfIntegers.exponent θ : 𝓞 K) * x) =
      g ((RingOfIntegers.exponent θ : 𝓞 K) * x) := by
    rw [← hQ]
    change f.toIntAlgHom (aeval θ Q) = g.toIntAlgHom (aeval θ Q)
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    exact congrArg (fun z => aeval z Q) hθ
  simp only [map_mul, map_natCast] at H
  exact mul_left_cancel₀ hn H

/-- The residue homomorphism attached to an ideal of prime absolute norm. -/
noncomputable def primeNormIdealHom {p : ℕ} (hp : p.Prime)
    (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p}) : 𝓞 K →+* ZMod p := by
  letI : Finite (𝓞 K ⧸ I.1) := (Ideal.absNorm_ne_zero_iff I.1).mp (by rw [I.2]; exact hp.ne_zero)
  letI := Fintype.ofFinite (𝓞 K ⧸ I.1)
  have hcard : Fintype.card (𝓞 K ⧸ I.1) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact I.2
  exact (ZMod.ringEquivOfPrime (𝓞 K ⧸ I.1) hp hcard).symm.toRingHom.comp (Ideal.Quotient.mk I.1)

theorem primeNormIdealHom_ker {p : ℕ} (hp : p.Prime)
    (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p}) : RingHom.ker (primeNormIdealHom hp I) = I.1 :=
        by
  unfold primeNormIdealHom
  rw [RingHom.ker_comp_of_injective _ (RingEquiv.injective _), Ideal.mk_ker]

/-- The polynomial root associated with a prime-norm ideal. -/
noncomputable def primeNormIdealRoot (θ : 𝓞 K) {p : ℕ} (hp : p.Prime)
    (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p}) : ResidueRoots (minpoly ℤ θ) p :=
  ⟨primeNormIdealHom hp I θ, by
    have H := congrArg (primeNormIdealHom hp I) (minpoly.aeval ℤ θ)
    change (primeNormIdealHom hp I).toIntAlgHom (aeval θ (minpoly ℤ θ)) = _ at H
    rw [← Polynomial.aeval_algHom_apply] at H
    simpa only [map_zero, aeval_def, algebraMap_int_eq, RingHom.toIntAlgHom_apply] using H⟩

theorem primeNormIdealRoot_injective (θ : 𝓞 K) {p : ℕ} (hp : p.Prime)
    (hc : p.Coprime (RingOfIntegers.exponent θ)) : Function.Injective (primeNormIdealRoot θ hp) :=
        by
  intro I J h
  have H := zmod_hom_ext_generator θ hp hc (congrArg Subtype.val h)
  apply Subtype.ext
  simpa only [primeNormIdealHom_ker] using congrArg RingHom.ker H

theorem rootCount_minpoly_eq_idealNormCount (θ : 𝓞 K) {p : ℕ} (hp : p.Prime)
    (hc : p.Coprime (RingOfIntegers.exponent θ)) :
    rootCount (minpoly ℤ θ) p = idealNormCount K p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  apply Nat.le_antisymm (rootCount_minpoly_le_card_ideals_norm θ hc)
  exact Nat.card_le_card_of_injective (primeNormIdealRoot θ hp) (primeNormIdealRoot_injective θ hp
      hc)

end NairTenenbaum
