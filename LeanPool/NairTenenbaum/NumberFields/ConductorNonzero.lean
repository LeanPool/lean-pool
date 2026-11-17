/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.ConductorQuotient
public import Mathlib.RingTheory.Discriminant

/-! # A primitive integral generator has nonzero conductor exponent

The discriminant of its rational power basis clears denominators in the
ring of integers. Thus the excluded conductor primes form a finite set.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial NumberField Ideal Algebra

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem ringOfIntegers_mem_adjoin_iff (θ x : 𝓞 K) :
    (x : K) ∈ Algebra.adjoin ℤ ({(θ : K)} : Set K) ↔
      x ∈ Algebra.adjoin ℤ ({θ} : Set (𝓞 K)) := by
  let e : 𝓞 K →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  have he : Function.Injective e := Subtype.val_injective
  change e x ∈ Algebra.adjoin ℤ ({e θ} : Set K) ↔ _
  rw [← e.map_adjoin_singleton, Subalgebra.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (he hxy) ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem exists_nonzero_integer_mem_conductor (θ : 𝓞 K) (B : PowerBasis ℚ K)
    (hB : B.gen = (θ : K)) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : 𝓞 K) ∈ conductor ℤ θ := by
  have hi : IsIntegral ℤ B.gen := hB.symm ▸ θ.property
  have hdint := Algebra.discr_isIntegral ℚ (fun i => show IsIntegral ℤ (B.basis i) from by
    rw [B.basis_eq_pow]
    exact hi.pow _)
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdint
  have hd₀ : d ≠ 0 := by
    intro h
    apply (Algebra.discr_isUnit_of_basis ℚ B.basis).ne_zero
    rw [← hd, h, map_zero]
  refine ⟨d, hd₀, mem_conductor_iff.mpr (fun z => ?_)⟩
  apply (ringOfIntegers_mem_adjoin_iff θ _).mp
  have H := Algebra.discr_mul_isIntegral_mem_adjoin ℚ hi z.property
  rw [← hd, algebraMap_smul, zsmul_eq_mul, hB] at H
  change (d : K) * (z : K) ∈ Algebra.adjoin ℤ ({(θ : K)} : Set K)
  exact H

theorem conductor_exponent_ne_zero (θ : 𝓞 K) (B : PowerBasis ℚ K)
    (hB : B.gen = (θ : K)) : RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨d, hd, hmem⟩ := exists_nonzero_integer_mem_conductor θ B hB
  have hdmem : d ∈ Ideal.under ℤ (conductor ℤ θ) := hmem
  have H := Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ θ))
  intro hzero
  change Ideal.absNorm (Ideal.under ℤ (conductor ℤ θ)) = 0 at hzero
  rw [hzero, Nat.cast_zero, Ideal.span_singleton_zero] at H
  rw [← H] at hdmem
  exact hd hdmem

end NairTenenbaum
