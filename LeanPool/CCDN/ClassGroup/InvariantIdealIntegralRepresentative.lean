/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.QuadraticInvariantIdeal
import LeanPool.CCDN.ClassGroup.FractionalIdealConjugation

/-! An invariant fractional ideal has an invariant integral
representative in the same ideal class. Multiplying a denominator by
its conjugate makes the denominator clearing compatible with the
involution. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- For an involutive ring automorphism `σ` of `R`, every `σ`-invariant invertible fractional ideal
`J` has a `σ`-invariant nonzero integral ideal `I` in the same ideal class. -/
theorem exists_invariant_integral_ideal_representative
    (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (J : (FractionalIdeal R⁰ K)ˣ)
    (hJ : fractionalIdealUnitAction (K := K) σ J = J) :
    ∃ I : (Ideal R)⁰,
      (I : Ideal R).map σ.toRingHom = I ∧
      ClassGroup.mk0 I = ClassGroup.mk K J := by
  let a : R := (J : FractionalIdeal R⁰ K).den
  have ha : a ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (J : FractionalIdeal R⁰ K).den.property
  have hσa : σ a ≠ 0 := by
    simpa only [map_zero] using σ.injective.ne ha
  let u : Kˣ := Units.mk0 (algebraMap R K (σ a * a)) (by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne (mul_ne_zero hσa ha))
  let I : Ideal R := Ideal.span {σ a} * (J : FractionalIdeal R⁰ K).num
  have hI : (I : FractionalIdeal R⁰ K) = (toPrincipalIdeal R K u * J :
      (FractionalIdeal R⁰ K)ˣ) := by
    simp only [I, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      Units.val_mul, coe_toPrincipalIdeal]
    rw [← (J : FractionalIdeal R⁰ K).den_mul_self_eq_num']
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R K (σ a)) *
        (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) * (J : FractionalIdeal R⁰ K)) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K (σ a * a)) * (J : FractionalIdeal R⁰ K)
    rw [map_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton, mul_assoc]
  have hI0 : I ≠ 0 := by
    intro hh
    exact (toPrincipalIdeal R K u * J).ne_zero
      (hI.symm.trans (by rw [hh]; exact FractionalIdeal.coeIdeal_bot))
  let I₀ : (Ideal R)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
  have hIu : FractionalIdeal.mk0 K I₀ = toPrincipalIdeal R K u * J := Units.ext hI
  have hσu : Units.map
      (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K).toMonoidHom u = u := by
    apply Units.ext
    change (IsFractionRing.ringEquivOfRingEquiv σ : K ≃+* K)
      (algebraMap R K (σ a * a)) = algebraMap R K (σ a * a)
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_mul, hσ, mul_comm]
  have hIfixed : fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I₀) =
      FractionalIdeal.mk0 K I₀ := by
    rw [hIu, map_mul, fractionalIdealUnitAction_principal, hσu, hJ]
  refine ⟨I₀, ?_, ?_⟩
  · apply FractionalIdeal.coeIdeal_inj (K := K) |>.mp
    have h := congrArg (fun U : (FractionalIdeal R⁰ K)ˣ =>
      (U : FractionalIdeal R⁰ K)) hIfixed
    change FractionalIdeal.ringEquivOfRingEquiv K K σ (I : FractionalIdeal R⁰ K) =
      (I : FractionalIdeal R⁰ K) at h
    simpa only [fractionalIdeal_conjugate_coeIdeal] using h
  · rw [← ClassGroup.mk_mk0 K I₀, hIu, map_mul, classGroup_mk_principal, one_mul]

end
end CCDN
