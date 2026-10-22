/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-! Rescaling an integral ideal by an element of its inverse ideal preserves
its class and carries the chosen generator of its square to the exact
generator alpha*kappa^2. This retains the generator needed for subsequent
archimedean estimates, rather than replacing it by an unspecified associate. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors
open FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Rescaling an integral ideal `I` with `I ^ 2 = (α)` by a nonzero `κ ∈ I⁻¹` gives an integral
ideal `J = κ I` in the same class with `J ^ 2 = (β)` for the exact generator `β = α * κ ^ 2`. -/
theorem rescale_integral_ideal_square (I : (Ideal R)⁰) {α : R} (hα : α ≠ 0)
    (hIα : (I : Ideal R) ^ 2 = Ideal.span {α})
    {κ : K} (hκ : κ ≠ 0) (hκI : κ ∈ (I : FractionalIdeal R⁰ K)⁻¹) :
    ∃ J : (Ideal R)⁰, ∃ β : R,
      ClassGroup.mk0 J = ClassGroup.mk0 I ∧ β ≠ 0 ∧
      algebraMap R K β = algebraMap R K α * κ ^ 2 ∧
      (J : Ideal R) ^ 2 = Ideal.span {β} ∧
      (J : FractionalIdeal R⁰ K) = spanSingleton R⁰ κ * (I : FractionalIdeal R⁰ K) := by
  let F : FractionalIdeal R⁰ K := spanSingleton R⁰ κ * (I : FractionalIdeal R⁰ K)
  have hI0 : (I : FractionalIdeal R⁰ K) ≠ 0 :=
    coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I)
  have hF0 : F ≠ 0 := mul_ne_zero (spanSingleton_ne_zero_iff.mpr hκ) hI0
  have hFle : F ≤ 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_singleton_mul.mp hx
    exact (mem_inv_iff hI0).mp hκI y hy
  obtain ⟨J₀, hJ₀⟩ := le_one_iff_exists_coeIdeal.mp hFle
  have hJ0 : J₀ ≠ 0 := by
    intro h
    apply hF0
    simp [← hJ₀, h]
  let J : (Ideal R)⁰ := ⟨J₀, mem_nonZeroDivisors_of_ne_zero hJ0⟩
  have hJ : (J : FractionalIdeal R⁰ K) = F := hJ₀
  have hsq : (J : FractionalIdeal R⁰ K) ^ 2 =
      spanSingleton R⁰ (algebraMap R K α * κ ^ 2) := by
    rw [hJ]
    dsimp only [F]
    rw [mul_pow, ← coeIdeal_pow, hIα, coeIdeal_span_singleton,
      spanSingleton_pow, spanSingleton_mul_spanSingleton, mul_comm]
  have hβmem : algebraMap R K α * κ ^ 2 ∈ (1 : FractionalIdeal R⁰ K) := by
    have hsle : (J : FractionalIdeal R⁰ K) ^ 2 ≤ 1 := by
      rw [← coeIdeal_pow]
      exact coeIdeal_le_one
    rw [hsq] at hsle
    exact spanSingleton_le_iff_mem.mp hsle
  obtain ⟨β, hβ⟩ := (mem_one_iff R⁰).mp hβmem
  have hβ0 : β ≠ 0 := by
    intro hb
    have hαK : algebraMap R K α ≠ 0 := by
      intro hz
      apply hα
      apply IsFractionRing.injective R K
      simpa using hz
    have hn := mul_ne_zero hαK (pow_ne_zero 2 hκ)
    exact hn (by rw [← hβ, hb, map_zero])
  refine ⟨J, β, ?_, hβ0, hβ, ?_, hJ⟩
  · apply Eq.symm
    apply (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring K).mpr
    exact ⟨κ, hκ, hJ.symm⟩
  · apply coeIdeal_injective (K := K)
    change (((J : Ideal R) ^ 2 : Ideal R) : FractionalIdeal R⁰ K) =
      ((Ideal.span {β} : Ideal R) : FractionalIdeal R⁰ K)
    rw [coeIdeal_pow, coeIdeal_span_singleton, hβ]
    exact hsq

end
end CCDN
