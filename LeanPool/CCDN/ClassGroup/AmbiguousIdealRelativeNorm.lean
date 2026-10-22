/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import LeanPool.CCDN.ForMathlib.ClassGroupAction

/-! Scalar comparisons for ambiguous ideal classes have relative norm
equal to a unit of the base ring. This formulation works directly with
relative ideal norms, so it does not identify the unit obstruction with
the trivial class. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped nonZeroDivisors

variable (R S : Type*) [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]

private theorem ambiguous_ideal_scalar_relative_unit
    (σ : S ≃ₐ[R] S) (I : (Ideal S)⁰)
    (hI : ClassGroup.mulEquiv σ.toRingEquiv (ClassGroup.mk0 I) = ClassGroup.mk0 I) :
    ∃ x y : S, ∃ u : Rˣ, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * (I : Ideal S).map σ.toRingHom =
        Ideal.span {y} * (I : Ideal S) ∧
      Algebra.intNorm R S x * (u : R) = Algebra.intNorm R S y := by
  rw [classGroup_mulEquiv_mk0] at hI
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hI
  change Ideal.span {x} * (I : Ideal S).map σ.toRingHom =
    Ideal.span {y} * (I : Ideal S) at hxy
  have hn := congrArg (Ideal.relNorm R) hxy
  simp only [map_mul, Ideal.relNorm_singleton] at hn
  have hnmap : Ideal.relNorm R ((I : Ideal S).map σ.toRingHom) =
      Ideal.relNorm R (I : Ideal S) := Ideal.relNorm_map_algEquiv σ I
  rw [hnmap] at hn
  have hnI : Ideal.relNorm R (I : Ideal S) ≠ 0 := by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      (Ideal.relNorm_eq_bot_iff.mp h)
  have hspan := mul_right_cancel₀ hnI hn
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact ⟨x, y, u, hx, hy, hxy, hu⟩

section NumberFields
open NumberField
open scoped NumberField

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]

/-- For number fields, the concrete scalar comparison has field norm
equal to a base-field unit. -/
theorem ambiguous_numberField_ideal_norm_unit
    (σ : K ≃ₐ[F] K) (I : (Ideal (𝓞 K))⁰)
    (hI : ClassGroup.mulEquiv (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
      (ClassGroup.mk0 I) = ClassGroup.mk0 I) :
    ∃ x y : 𝓞 K, ∃ u : (𝓞 F)ˣ, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span {x} * (I : Ideal (𝓞 K)).map
        (RingOfIntegers.mapAlgEquiv σ).toRingHom =
        Ideal.span {y} * (I : Ideal (𝓞 K)) ∧
      Algebra.norm F ((y : K) / (x : K)) = ((u : 𝓞 F) : F) := by
  obtain ⟨x, y, u, hx, hy, hxy, hu⟩ :=
    ambiguous_ideal_scalar_relative_unit (𝓞 F) (𝓞 K) (RingOfIntegers.mapAlgEquiv σ) I hI
  refine ⟨x, y, u, hx, hy, hxy, ?_⟩
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hn := congrArg (algebraMap (𝓞 F) F) hu
  rw [map_mul, Algebra.algebraMap_intNorm (K := F) (L := K),
    Algebra.algebraMap_intNorm (K := F) (L := K)] at hn
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, ← div_eq_mul_inv]
  apply (div_eq_iff (Algebra.norm_ne_zero_iff.mpr hxK)).mpr
  exact hn.symm.trans (mul_comm _ _)

end NumberFields

end
end CCDN
