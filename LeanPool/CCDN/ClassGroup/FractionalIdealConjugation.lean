/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ClassGroup.QuadraticInvariantIdeal

/-! Compatibility of conjugation with integral representatives and with
the scalar comparisons used in the definition of an ideal class. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Applying a ring automorphism `σ` of `R` to the fractional ideal of an integral ideal `I` gives
the fractional ideal of the integral ideal `I.map σ`. -/
theorem fractionalIdeal_conjugate_coeIdeal (σ : R ≃+* R) (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K K σ (I : FractionalIdeal R⁰ K) =
      (I.map σ.toRingHom : FractionalIdeal R⁰ K) := by
  let : RingHomInvPair (σ : R →+* R) σ.symm := RingHomInvPair.of_ringEquiv σ
  let : RingHomInvPair (σ.symm : R →+* R) σ := RingHomInvPair.of_ringEquiv σ.symm
  ext x
  change x ∈ (Submodule.map
    (IsFractionRing.semilinearEquivOfRingEquiv K K σ).toLinearMap
      (I : FractionalIdeal R⁰ K).val) ↔
    x ∈ (I.map σ.toRingHom : FractionalIdeal R⁰ K)
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
    apply (FractionalIdeal.mem_coeIdeal R⁰).mpr
    refine ⟨σ r, Ideal.mem_map_of_mem _ hr, ?_⟩
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ r).symm
  · intro hx
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hx
    obtain ⟨s, hs, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective σ.toRingHom σ.surjective).mp hr
    refine ⟨algebraMap R K s, (FractionalIdeal.mem_coeIdeal R⁰).mpr
      ⟨s, hs, rfl⟩, ?_⟩
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap σ s

/-- If `(x) * σ(I) = (y) * I` for nonzero `x y : R`, then the conjugate of the fractional ideal of
`I` under `σ` equals the principal fractional ideal of `y / x` times that of `I`. -/
theorem integral_ideal_scalar_fractional_comparison
    (σ : R ≃+* R) (I : (Ideal R)⁰) (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : Ideal.span {x} * (I : Ideal R).map σ.toRingHom =
      Ideal.span {y} * (I : Ideal R)) :
    fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
      toPrincipalIdeal R K
        (Units.mk0 (algebraMap R K y) (by
          simpa only [map_zero] using (IsFractionRing.injective R K).ne hy) /
        Units.mk0 (algebraMap R K x) (by
          simpa only [map_zero] using (IsFractionRing.injective R K).ne hx)) *
      FractionalIdeal.mk0 K I := by
  let a : Kˣ := Units.mk0 (algebraMap R K x) (by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hx)
  let b : Kˣ := Units.mk0 (algebraMap R K y) (by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hy)
  have h : toPrincipalIdeal R K a *
      fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
      toPrincipalIdeal R K b * FractionalIdeal.mk0 K I := by
    apply Units.ext
    have hh := congrArg (fun J : Ideal R => (J : FractionalIdeal R⁰ K)) hxy
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] at hh
    simp only [Units.val_mul, coe_toPrincipalIdeal, fractionalIdealUnitAction,
      Units.coe_map, FractionalIdeal.coe_mk0]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R K x) *
      FractionalIdeal.ringEquivOfRingEquiv K K σ (I : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K y) * (I : FractionalIdeal R⁰ K)
    rw [fractionalIdeal_conjugate_coeIdeal]
    exact hh
  change fractionalIdealUnitAction (K := K) σ (FractionalIdeal.mk0 K I) =
    toPrincipalIdeal R K (b / a) * FractionalIdeal.mk0 K I
  rw [map_div]
  apply mul_left_cancel (a := toPrincipalIdeal R K a)
  rw [h]
  symm
  calc
    _ = (toPrincipalIdeal R K a * (toPrincipalIdeal R K a)⁻¹) *
        (toPrincipalIdeal R K b * FractionalIdeal.mk0 K I) := by
      rw [div_eq_mul_inv]
      ac_rfl
    _ = _ := by rw [mul_inv_cancel, one_mul]

end
end CCDN
