/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Tactic.FieldSimp
public import LeanPool.CommutativeAlgebraToolkit.InjectiveIffDivisible

/-!
# The module `K / A` for a fraction field `K` of `A`, and the dual of `A ⧸ tA`

`K / A` is written `K ⧸ LinearMap.range (Algebra.linearMap A K)`.

## Main statements

* `Ideal.injective_applyₗ_quotient_mk_one`, `Ideal.range_applyₗ_quotient_mk_one`: evaluation at
  the class of `1` identifies `Hom(A ⧸ tA, M)` with the part of `M` killed by `t`.
* `IsFractionRing.ker_toSpanSingleton_inv`, `IsFractionRing.range_toSpanSingleton_inv`: for
  `t ≠ 0`, the map `a ↦ a / t mod A` has kernel `tA` and image the part of `K / A` killed by `t`.
* `IsFractionRing.smul_surjective_quotient_range`: `K / A` is divisible.
* `IsFractionRing.baer_quotient_range`: over a principal ideal ring, `K / A` satisfies Baer's
  criterion, so it is injective.
* `Module.IsTorsion.isArtinian`: a finitely generated torsion module over a principal ideal
  domain is Artinian.
-/

public section

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]

/-- A class `k mod A` vanishes in `K/A` exactly when `k` comes from `A`. -/
private theorem quotient_range_linearMap_mk_eq_zero_iff (k : K) :
    (Submodule.Quotient.mk k : K ⧸ LinearMap.range (Algebra.linearMap A K)) = 0 ↔
      ∃ a : A, algebraMap A K a = k := by
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  simp [Algebra.linearMap_apply]

/-- A linear map on `A/I` is determined by its value at the class of `1`. -/
theorem Ideal.injective_applyₗ_quotient_mk_one {M : Type*} [AddCommGroup M] [Module A M]
    (I : Ideal A) :
    Function.Injective
      (LinearMap.applyₗ (Submodule.Quotient.mk 1 : A ⧸ I) : (A ⧸ I →ₗ[A] M) →ₗ[A] M) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ LinearMap.ext fun y ↦ ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have : (Submodule.Quotient.mk a : A ⧸ I) = a • Submodule.Quotient.mk 1 := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  simp only [LinearMap.applyₗ_apply_apply] at hf
  rw [this, map_smul, hf, smul_zero, LinearMap.zero_apply]

/-- Evaluation at the class of `1` identifies `Hom(A/tA, M)` with the submodule of `M` killed
by `t`. -/
theorem Ideal.range_applyₗ_quotient_mk_one {M : Type*} [AddCommGroup M] [Module A M] (t : A) :
    LinearMap.range (LinearMap.applyₗ (Submodule.Quotient.mk 1 : A ⧸ Ideal.span {t}) :
      (A ⧸ Ideal.span {t} →ₗ[A] M) →ₗ[A] M) = Submodule.torsionBy A M t := by
  ext q
  rw [LinearMap.mem_range, Submodule.mem_torsionBy_iff]
  constructor
  · rintro ⟨f, rfl⟩
    simp only [LinearMap.applyₗ_apply_apply]
    rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self t), map_zero]
  · intro hq
    have hle : Ideal.span {t} ≤ LinearMap.ker (LinearMap.toSpanSingleton A _ q) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.toSpanSingleton_apply, hq]
    refine ⟨(Ideal.span {t}).liftQ _ hle, ?_⟩
    simp only [LinearMap.applyₗ_apply_apply]
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

namespace IsFractionRing

/-- The map `a ↦ a/t mod A`, from `A` to `K/A`, sends `a` to the class of `a t⁻¹`. -/
private theorem toSpanSingleton_inv_apply (t a : A) :
    LinearMap.toSpanSingleton A (K ⧸ LinearMap.range (Algebra.linearMap A K))
        (Submodule.Quotient.mk (algebraMap A K t)⁻¹) a =
      Submodule.Quotient.mk (algebraMap A K a * (algebraMap A K t)⁻¹) := by
  rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def]

variable [IsFractionRing A K]

/-- For `t ≠ 0`, the kernel of `a ↦ a/t mod A` is `tA`. -/
theorem ker_toSpanSingleton_inv {t : A} (ht : t ≠ 0) :
    LinearMap.ker (LinearMap.toSpanSingleton A (K ⧸ LinearMap.range (Algebra.linearMap A K))
      (Submodule.Quotient.mk (algebraMap A K t)⁻¹)) = Ideal.span {t} := by
  have ht' : algebraMap A K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht
  ext a
  rw [LinearMap.mem_ker, toSpanSingleton_inv_apply,
    quotient_range_linearMap_mk_eq_zero_iff, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hb, inv_mul_cancel_right₀ ht']
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [map_mul, mul_inv_cancel_right₀ ht']⟩

/-- For `t ≠ 0`, the image of `a ↦ a/t mod A` is the submodule `t⁻¹A/A` of `K/A` killed
by `t`. -/
theorem range_toSpanSingleton_inv {t : A} (ht : t ≠ 0) :
    LinearMap.range (LinearMap.toSpanSingleton A (K ⧸ LinearMap.range (Algebra.linearMap A K))
      (Submodule.Quotient.mk (algebraMap A K t)⁻¹)) =
      Submodule.torsionBy A (K ⧸ LinearMap.range (Algebra.linearMap A K)) t := by
  have ht' : algebraMap A K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht
  ext q
  rw [LinearMap.mem_range, Submodule.mem_torsionBy_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [toSpanSingleton_inv_apply, ← Submodule.Quotient.mk_smul, Algebra.smul_def,
      quotient_range_linearMap_mk_eq_zero_iff]
    exact ⟨a, by field_simp⟩
  · intro hq
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def,
      quotient_range_linearMap_mk_eq_zero_iff] at hq
    obtain ⟨b, hb⟩ := hq
    refine ⟨b, ?_⟩
    rw [toSpanSingleton_inv_apply, hb]
    congr 1
    field_simp

/-- `K/A` is divisible: every `r ≠ 0` acts surjectively. -/
theorem smul_surjective_quotient_range {r : A} (hr : r ≠ 0) :
    Function.Surjective
      (fun q : K ⧸ LinearMap.range (Algebra.linearMap A K) ↦ r • q) := by
  have hr' : algebraMap A K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hr
  intro q
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ((algebraMap A K r)⁻¹ * k), ?_⟩
  simp only
  rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, mul_inv_cancel_left₀ hr']

variable (A K) in
/-- Over a principal ideal ring, `K/A` satisfies Baer's criterion. -/
theorem baer_quotient_range [IsPrincipalIdealRing A] :
    Module.Baer A (K ⧸ LinearMap.range (Algebra.linearMap A K)) :=
  Module.Baer.of_smul_surjective fun _ hr ↦ smul_surjective_quotient_range hr

end IsFractionRing

/-- A finitely generated torsion module over a principal ideal domain is Artinian. -/
theorem Module.IsTorsion.isArtinian [IsDomain A] [IsPrincipalIdealRing A] {E : Type*}
    [AddCommGroup E] [Module A E] [Module.Finite A E] (hE : Module.IsTorsion A E) :
    IsArtinian A E := by
  classical
  obtain ⟨ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_directSum_of_isTorsion hE
  have hM : ∀ i, IsArtinian A (A ⧸ A ∙ p i ^ e i) := fun i ↦
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (isFiniteLength_quotient_span_singleton A
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (hp i).ne_zero)))).2
  exact isArtinian_of_linearEquiv ((DirectSum.linearEquivFunOnFintype A ι _).symm.trans f.symm)
