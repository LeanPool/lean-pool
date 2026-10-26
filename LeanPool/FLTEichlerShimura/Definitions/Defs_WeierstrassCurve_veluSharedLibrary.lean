/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

/-
Extracted from Prove2Me proofs by Claude (2026-09-05):
* WeierstrassCurve.velu_map_equation_of_oddOrderSummingSet
  (99841a34-31c0-570f-ae9f-f8802f859369), submission
  368c886c-4d95-5623-a9cf-0bde6782ce35.
* WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq
  (acd8e718-18d4-56b2-b4fe-299ba6bb61cd), submission
  200e3821-d296-5b22-a15a-da3c41ece41b.
-/

module

public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_OddOrderSummingSet
public import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_VeluPointMap
public import LeanPool.FLTEichlerShimura.Definitions.Defs_IsogenyEndDatum_sharedLibrary

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import LeanPool.FLTEichlerShimura.Definitions.Def_WeierstrassCurve_RatPointHom
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import LeanPool.FLTEichlerShimura.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add_v2
import Mathlib.Tactic.NormNum.Prime
import LeanPool.FLTEichlerShimura.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Logic.Equiv.PartialEquiv

/-!
# Shared library for the odd-order Vélu construction

Declarations common to the quotient-equation and function-field-isogeny proofs, together with
their supporting helpers. Namespaces are rooted directly in `AlgebraicCurve`, `WeierstrassCurve`,
and the other mathematical namespaces; no Prove2Me namespace aliases are used.

This library is used by the quotient-equation and function-field-isogeny proof files.
-/

section privateSection

open Polynomial IsDedekindDomain WithZero IsLocalRing WeierstrassCurve Affine Point
  CoordinateRing AlgebraicCurve

open scoped Polynomial.Bivariate Pointwise nonZeroDivisors

section

section

open Ideal hiding map_mul

open Module

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

namespace CoordinateRing

theorem exists_eq_XYIdeal_of_isMaximal [IsAlgClosed F] (𝔪 : Ideal W.CoordinateRing)
    (h𝔪 : 𝔪.IsMaximal) : ∃ x y : F, W.Equation x y ∧ XYIdeal W x (C y) = 𝔪 := by
  have := h𝔪
  let : Field (W.CoordinateRing ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : Module.Finite F (W.CoordinateRing ⧸ 𝔪) :=
    finite_of_finite_type_of_isJacobsonRing F (W.CoordinateRing ⧸ 𝔪)
  have he : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ 𝔪)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨x, hx⟩ := he.2 (Ideal.Quotient.mk 𝔪 (mk W (Polynomial.C Polynomial.X)))
  obtain ⟨y, hy⟩ := he.2 (Ideal.Quotient.mk 𝔪 (mk W Y))
  have hconst : ∀ a : F, Ideal.Quotient.mk 𝔪 ((mk W) (Polynomial.C (Polynomial.C a)))
      = algebraMap F (W.CoordinateRing ⧸ 𝔪) a := by
    intro a
    have h1 : (mk W) (Polynomial.C (Polynomial.C a)) = algebraMap F W.CoordinateRing a := by
      rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
        Algebra.algebraMap_self_apply]
      rfl
    rw [h1, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have key : ((Ideal.Quotient.mk 𝔪).comp
        (mk W : Polynomial (Polynomial F) →+* W.CoordinateRing)) =
      (algebraMap F (W.CoordinateRing ⧸ 𝔪)).comp
        ((Polynomial.evalRingHom x).comp (Polynomial.evalRingHom (Polynomial.C y))) := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext (fun a => ?_) ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      exact hconst a
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.eval_C]
      exact hx.symm
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.eval_C]
      exact hy.symm
  have heval : W.Equation x y := by
    have h0 := DFunLike.congr_fun key W.polynomial
    simp only [RingHom.comp_apply, AdjoinRoot.mk_self, _root_.map_zero,
      Polynomial.coe_evalRingHom] at h0
    exact (map_eq_zero_iff (algebraMap F (W.CoordinateRing ⧸ 𝔪)) he.1).mp h0.symm
  have hXmem : XClass W x ∈ 𝔪 := by
    have h2 : ((Ideal.Quotient.mk 𝔪).comp (mk W))
        (Polynomial.C (Polynomial.X - Polynomial.C x)) = 0 := by
      rw [key]
      simp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  have hYmem : YClass W (Polynomial.C y) ∈ 𝔪 := by
    have h2 : ((Ideal.Quotient.mk 𝔪).comp (mk W))
        (Y - Polynomial.C (Polynomial.C y)) = 0 := by
      rw [key]
      simp
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact h2
  refine ⟨x, y, heval, ?_⟩
  have hXY_le : XYIdeal W x (Polynomial.C y) ≤ 𝔪 := by
    rw [XYIdeal, Ideal.span_le]
    rintro _ (rfl | rfl)
    · exact hXmem
    · exact hYmem
  have hXY_max : (XYIdeal W x (Polynomial.C y)).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      ((quotientXYIdealEquiv (W' := W) (x := x) (y := Polynomial.C y)
        heval).toMulEquiv.isField (Field.toIsField F))
  exact hXY_max.eq_of_le h𝔪.ne_top hXY_le

end CoordinateRing
end Affine
end WeierstrassCurve
end
section

section

universe u

namespace WeierstrassCurve
namespace Affine
namespace Point

variable {R : Type u} [CommRing R] {W : Affine R}

def xOrZero : W.Point → R
  | .zero => 0
  | .some x _ _ => x

@[scoped simp] lemma xOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).xOrZero = x := rfl

end Point
end Affine

end WeierstrassCurve
end
section

namespace WeierstrassCurve
section BaseChange

variable {R : Type*} {A : Type*} [CommRing R] [CommRing A] (W : WeierstrassCurve R) (f : R →+* A)

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, _root_.map_neg, map_add, map_sub, map_mul, map_pow])

@[scoped simp] public lemma map_veluGx (x y : R) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, map_a₁, map_a₂, map_a₄]
  map_simp

@[scoped simp] public lemma map_veluGy (x y : R) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [veluGy, map_a₁, map_a₃]
  map_simp

@[scoped simp] public lemma map_veluT (x y : R) :
    (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp only [veluT_eq, map_b₂, map_b₄]
  map_simp

@[scoped simp] public lemma map_veluU (x y : R) :
    (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp only [veluU, map_veluGy, map_pow]

@[scoped simp] lemma map_veluW (x y : R) :
    (W.map f).veluW (f x) (f y) = f (W.veluW x y) := by
  simp only [veluW, map_veluU, map_veluT, map_add, map_mul]

lemma map_veluTSum (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluTSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluTSum S) := by
  rw [veluTSum, veluTSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT]

lemma map_veluWSum (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluWSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluWSum S) := by
  rw [veluWSum, veluWSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluW]

public lemma map_veluQuotient (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluQuotient (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = (W.veluQuotient S).map f := by
  ext
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp only [veluQuotient_a₄, map_a₄, map_veluTSum _ _ S hf]
    map_simp
  · simp only [veluQuotient_a₆, map_a₆, map_b₂, map_veluTSum _ _ S hf, map_veluWSum _ _ S hf]
    map_simp

end BaseChange
end WeierstrassCurve
end

section

section

open FractionalIdeal

namespace FractionalIdeal
variable {R : Type*} (K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem isUnit_coeIdeal_of_forall_isMaximal [IsNoetherianRing R]
    (hmax : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 ≠ ⊥ → IsUnit (𝔪 : FractionalIdeal R⁰ K))
    (I : Ideal R) : I ≠ ⊥ → IsUnit (I : FractionalIdeal R⁰ K) := by
  refine IsNoetherian.induction
    (P := fun I : Ideal R => I ≠ ⊥ → IsUnit (I : FractionalIdeal R⁰ K)) (fun I ih hI => ?_) I
  rcases eq_or_ne I ⊤ with rfl | hItop
  · rw [coeIdeal_top]
    exact isUnit_one
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hItop
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hI𝔪))
  have h𝔪unit : IsUnit (𝔪 : FractionalIdeal R⁰ K) := hmax 𝔪 h𝔪 h𝔪0
  have h𝔪inv : (𝔪 : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹ = 1 :=
    (mul_inv_cancel_iff_isUnit K).mpr h𝔪unit
  have hle : (I : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹ ≤ 1 := by
    calc (I : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹
        ≤ (𝔪 : FractionalIdeal R⁰ K) * (𝔪 : FractionalIdeal R⁰ K)⁻¹ := by gcongr
      _ = 1 := h𝔪inv
  obtain ⟨J, hJ⟩ := le_one_iff_exists_coeIdeal.mp hle
  have hJ𝔪 : J * 𝔪 = I := by
    rw [← coeIdeal_inj (K := K), coeIdeal_mul, hJ, mul_assoc,
      mul_comm (𝔪 : FractionalIdeal R⁰ K)⁻¹, h𝔪inv, mul_one]
  have hIJ : I ≤ J := hJ𝔪 ▸ Ideal.mul_le_left
  have hJ0 : J ≠ ⊥ := fun h => hI (le_bot_iff.mp (h ▸ hIJ))
  have hne : I ≠ J := by
    rintro rfl
    have hsmul : I ≤ 𝔪 • I := by
      rw [Ideal.smul_eq_mul, mul_comm]
      exact le_of_eq hJ𝔪.symm
    obtain ⟨r, hr𝔪, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 I
      (IsNoetherian.noetherian I) hsmul
    obtain ⟨n, hnI, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hr0 : r = 0 := by
      have hrn := hr n hnI
      rw [smul_eq_mul] at hrn
      exact (mul_eq_zero.mp hrn).resolve_right hn0
    exact h𝔪.ne_top (𝔪.eq_top_of_isUnit_mem (by simpa [hr0] using hr𝔪) isUnit_one.neg)
  have hJunit : IsUnit (J : FractionalIdeal R⁰ K) := ih J (lt_of_le_of_ne hIJ hne) hJ0
  rw [← hJ𝔪, coeIdeal_mul]
  exact hJunit.mul h𝔪unit

theorem isUnit_of_forall_isMaximal [IsNoetherianRing R]
    (hmax : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 ≠ ⊥ → IsUnit (𝔪 : FractionalIdeal R⁰ K))
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) : IsUnit I := by
  obtain ⟨a, J, ha, rfl⟩ := exists_eq_spanSingleton_mul I
  have ha' : algebraMap R K a ≠ 0 := mt IsFractionRing.to_map_eq_zero_iff.mp ha
  refine IsUnit.mul ?_ (isUnit_coeIdeal_of_forall_isMaximal K hmax J ?_)
  · exact isUnit_iff_exists_inv.mpr ⟨spanSingleton R⁰ (algebraMap R K a), by
      rw [spanSingleton_mul_spanSingleton, inv_mul_cancel₀ ha', spanSingleton_one]⟩
  · rintro rfl
    simp at hI

end FractionalIdeal
theorem isDedekindDomain_of_forall_isMaximal_isUnit {R : Type*} (K : Type*) [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R]
    (hmax : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → 𝔪 ≠ ⊥ → IsUnit (𝔪 : FractionalIdeal R⁰ K)) :
    IsDedekindDomain R :=
  (isDedekindDomain_iff_mul_inv_cancel (K := K)).mpr fun I hI =>
    (mul_inv_cancel_iff_isUnit K).mpr (isUnit_of_forall_isMaximal K hmax I hI)

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

namespace CoordinateRing

theorem isUnit_coeIdeal_of_isMaximal [IsAlgClosed F] (hΔ : W.Δ ≠ 0)
    {𝔪 : Ideal W.CoordinateRing} (h𝔪 : 𝔪.IsMaximal) :
    IsUnit (𝔪 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) := by
  obtain ⟨x, y, hxy, hXY⟩ := exists_eq_XYIdeal_of_isMaximal 𝔪 h𝔪
  rw [← hXY, ← XYIdeal'_eq ((W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hxy)]
  exact (XYIdeal' _).isUnit

public theorem isDedekindDomain_of_Δ_ne_zero [IsAlgClosed F] (hΔ : W.Δ ≠ 0) :
    IsDedekindDomain W.CoordinateRing :=
  isDedekindDomain_of_forall_isMaximal_isUnit W.FunctionField
    fun _𝔪 h𝔪 _ => isUnit_coeIdeal_of_isMaximal hΔ h𝔪

end CoordinateRing
end Affine
end WeierstrassCurve
end
section

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem deg_eq_one_of_surjective (v : Place K F)
    (h : Function.Surjective (algebraMap K v.ResidueField)) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    ⟨(algebraMap K v.ResidueField).injective, h⟩
  change Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable [Algebra K R] [IsScalarTower K R F]

theorem deg_ofHeightOneSpectrum_eq_one (w : HeightOneSpectrum R)
    (hw : ∀ r : R, ∃ c : K, r - algebraMap K R c ∈ w.asIdeal) :
    (ofHeightOneSpectrum (K := K) (F := F) w).deg = 1 := by
  set v : Place K F := ofHeightOneSpectrum (K := K) w with hv
  apply deg_eq_one_of_surjective
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, d, hd, hnd⟩ : ∃ (n d : R) (_ : d ∈ w.asIdeal.primeCompl),
      (a : F) * algebraMap R F d = algebraMap R F n := by
    obtain ⟨n, d, hcase | hcase⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := F) (a : F)
    · exact ⟨n, d, d.2, hcase⟩
    · refine ⟨(d : R), n, ?_, hcase⟩
      intro hn
      refine d.2 ?_
      replace hn : n ∈ w.asIdeal := hn
      change (d : R) ∈ w.asIdeal
      rw [← w.valuation_lt_one_iff_mem (K := F)] at hn ⊢
      calc w.valuation F (algebraMap R F (d : R))
          = w.valuation F (a : F) * w.valuation F (algebraMap R F n) := by
            rw [← map_mul, hcase]
        _ ≤ 1 * w.valuation F (algebraMap R F n) := mul_le_mul_left a.2 _
        _ = w.valuation F (algebraMap R F n) := one_mul _
        _ < 1 := hn
  obtain ⟨cn, hcn⟩ := hw n
  obtain ⟨cd, hcd⟩ := hw d
  have hcd0 : cd ≠ 0 := by
    rintro rfl
    rw [_root_.map_zero, sub_zero] at hcd
    exact hd hcd
  have hcdR : algebraMap K R cd ∉ w.asIdeal := fun hmem =>
    hd (by simpa using w.asIdeal.add_mem hcd hmem)
  have hvd : w.valuation F (algebraMap R F d) = 1 :=
    le_antisymm (w.valuation_le_one d)
      (not_lt.mp fun hlt => hd ((w.valuation_lt_one_iff_mem (K := F) d).mp hlt))
  have hvcd : w.valuation F (algebraMap K F cd) = 1 := by
    rw [IsScalarTower.algebraMap_apply K R F]
    exact le_antisymm (w.valuation_le_one _)
      (not_lt.mp fun hlt => hcdR ((w.valuation_lt_one_iff_mem (K := F) _).mp hlt))
  have hcdF : algebraMap K F cd ≠ 0 := by
    simpa using hcd0
  refine ⟨cn / cd, ?_⟩
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]
  refine (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal v.toValuationSubring)).mpr ?_
  have hmem : algebraMap K R cn * d - algebraMap K R cd * n ∈ w.asIdeal := by
    have heq : algebraMap K R cn * d - algebraMap K R cd * n
        = -((n - algebraMap K R cn) * d) + n * (d - algebraMap K R cd) := by ring
    rw [heq]
    exact w.asIdeal.add_mem (w.asIdeal.neg_mem (w.asIdeal.mul_mem_right _ hcn))
      (w.asIdeal.mul_mem_left _ hcd)
  have key : ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
      * (algebraMap K F cd * algebraMap R F d)
      = algebraMap R F (algebraMap K R cn * d - algebraMap K R cd * n) := by
    rw [coe_algebraMap, map_div₀, map_sub, map_mul, map_mul]
    simp only [← IsScalarTower.algebraMap_apply K R F]
    field_simp
    linear_combination (-(algebraMap K F cd)) * hnd
  refine (Valuation.mem_maximalIdeal_iff (v := w.valuation F)).mpr ?_
  change w.valuation F ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F)) < 1
  calc w.valuation F ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
      = w.valuation F ((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
        * (w.valuation F (algebraMap K F cd) * w.valuation F (algebraMap R F d)) := by
          rw [hvcd, hvd, one_mul, mul_one]
    _ = w.valuation F (((algebraMap K v.toValuationSubring (cn / cd) : F) - (a : F))
        * (algebraMap K F cd * algebraMap R F d)) := by rw [map_mul, map_mul]
    _ = w.valuation F (algebraMap R F (algebraMap K R cn * d - algebraMap K R cd * n)) := by
          rw [key]
    _ < 1 := (w.valuation_lt_one_iff_mem (K := F) _).mpr hmem

end Place
end AlgebraicCurve
namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

variable [IsDedekindDomain W.CoordinateRing]

theorem deg_placeOfEquation {x y : F} (h : W.Equation x y) : (placeOfEquation h).deg = 1 :=
  AlgebraicCurve.Place.deg_ofHeightOneSpectrum_eq_one _ (exists_sub_algebraMap_mem h)

end Affine
end WeierstrassCurve
end
section

namespace WeierstrassCurve
namespace Affine
namespace Point

variable {R : Type*} [CommRing R] {W : Affine R}

lemma coordsOrZero_fst (P : W.Point) : P.coordsOrZero.1 = P.xOrZero := by
  cases P <;> rfl

end Point
end Affine
section OrderArithmetic

variable {G : Type*} [AddCommGroup G]

lemma nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd {Q : G} {p : ℕ}
    (hord : addOrderOf Q = p) {k : ℕ} (hk : ¬ p ∣ k) : k • Q ≠ 0 := fun h =>
  hk (hord ▸ (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h)

public lemma sub_nsmul_eq_neg_of_nsmul_eq_zero {Q : G} {p : ℕ} (hp : p • Q = 0) {k : ℕ}
    (hk : k ≤ p) : (p - k) • Q = -(k • Q) := by
  rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk, hp]

end OrderArithmetic
section IsOddVeluSet

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

omit [DecidableEq F] in
public lemma exists_some_of_ne_zero {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ (x y : F) (h : W.toAffine.Nonsingular x y), P = Point.some x y h ∧
      P.coordsOrZero = (x, y) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨x, y, h, rfl, rfl⟩

variable {Q : W.toAffine.Point} {p : ℕ}

lemma y_ne_negY_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    y ≠ W.toAffine.negY x y := fun hy =>
  h2 (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)

lemma veluGy_ne_zero_of_two_nsmul_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 : ℕ) • (Point.some x y h : W.toAffine.Point) ≠ 0) :
    W.veluGy x y ≠ 0 := by
  intro h0
  refine y_ne_negY_of_two_nsmul_ne_zero h h2 ?_
  have hkey : W.toAffine.negY x y = y + W.veluGy x y := by
    simp only [Affine.negY, veluGy]; ring
  rw [hkey, h0, add_zero]

end IsOddVeluSet
end WeierstrassCurve
end

section

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem isUnit_mk_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  have huf : (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      = (u : v.toValuationSubring) := Subtype.ext hu
  rw [huf]
  exact u.isUnit

theorem residue_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    residue v.toValuationSubring (⟨f, v.mem_of_ord_nonneg hf h.ge⟩ : v.toValuationSubring)
      ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (v.isUnit_mk_of_ord_eq_zero hf h)

theorem evalAt_ne_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f ≠ 0 := by
  intro h0
  have hres := v.algebraMap_evalAt hv (v.mem_of_ord_nonneg hf h.ge)
  rw [h0, _root_.map_zero] at hres
  exact v.residue_ne_zero_of_ord_eq_zero hf h hres.symm

theorem evalAt_algebraMap (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

theorem evalAt_mul (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
end AlgebraicCurve
end

section

section

namespace WeierstrassCurve
section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma veluY_summand_negY (x y : F) (Q : F × F) :
    W.veluU Q.1 Q.2 * (2 * W.toAffine.negY x y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
      + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + W.toAffine.negY x y - Q.2) / (x - Q.1) ^ 2
      + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2
    = W.a₁ * (W.veluT Q.1 Q.2 / (x - Q.1) + W.veluU Q.1 Q.2 / (x - Q.1) ^ 2)
      - (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) / (x - Q.1) ^ 3
        + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) / (x - Q.1) ^ 2
        + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) / (x - Q.1) ^ 2) := by
  rcases eq_or_ne x Q.1 with h | h
  · simp [h, sub_self]
  · have hd : x - Q.1 ≠ 0 := sub_ne_zero.mpr h
    simp only [veluT, veluU, veluGx, veluGy, Affine.negY]
    field_simp
    ring

lemma veluY_negY (S : Finset (F × F)) (x y : F) :
    W.veluY S x (W.toAffine.negY x y)
      = (W.veluQuotient S).toAffine.negY (W.veluX S x) (W.veluY S x y) := by
  simp only [veluY, veluX]
  rw [Finset.sum_congr rfl fun Q _ => W.veluY_summand_negY x y Q,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Affine.negY, veluQuotient_a₁, veluQuotient_a₃]
  ring

end Field
end WeierstrassCurve
end
section

noncomputable section

namespace WeierstrassCurve
section Corrections

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluXCorr (x₀ y₀ r : F) : F :=
  W.veluT x₀ y₀ / (r - x₀) + W.veluU x₀ y₀ / (r - x₀) ^ 2

def veluYCorr (x₀ y₀ r s : F) : F :=
  -(W.veluU x₀ y₀ * (2 * s + W.a₁ * r + W.a₃) / (r - x₀) ^ 3
    + W.veluT x₀ y₀ * (W.a₁ * (r - x₀) + s - y₀) / (r - x₀) ^ 2
    + (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (r - x₀) ^ 2)

theorem veluX_sub_self_eq_sum_veluXCorr (S : Finset (F × F)) (r : F) :
    W.veluX S r - r = ∑ Q ∈ S, W.veluXCorr Q.1 Q.2 r := by
  simp only [veluX, veluXCorr, add_sub_cancel_left]

theorem veluY_sub_self_eq_sum_veluYCorr (S : Finset (F × F)) (r s : F) :
    W.veluY S r s - s = ∑ Q ∈ S, W.veluYCorr Q.1 Q.2 r s := by
  unfold veluY veluYCorr
  rw [sub_sub_cancel_left, ← Finset.sum_neg_distrib]

end Corrections
section AlphaLaurent

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluXCorr_mul_r (x₀ y₀ : F) {r : F} (hr : r ≠ x₀) :
    W.veluXCorr x₀ y₀ r * r
      = W.veluT x₀ y₀ + W.veluW x₀ y₀ / (r - x₀) + W.veluU x₀ y₀ * x₀ / (r - x₀) ^ 2 := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  simp only [veluXCorr, veluW]
  field_simp
  ring

theorem veluX_sub_self_mul_r (S : Finset (F × F)) {r : F} (hr : ∀ A ∈ S, r ≠ A.1) :
    (W.veluX S r - r) * r
      = W.veluTSum S
        + ∑ Q ∈ S, (W.veluW Q.1 Q.2 / (r - Q.1) + W.veluU Q.1 Q.2 * Q.1 / (r - Q.1) ^ 2) := by
  rw [W.veluX_sub_self_eq_sum_veluXCorr, Finset.sum_mul, veluTSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun Q hQ => by
    rw [W.veluXCorr_mul_r Q.1 Q.2 (hr Q hQ)]; ring

end AlphaLaurent
end WeierstrassCurve
end
section

noncomputable section

namespace WeierstrassCurve
section Deficit

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The residual of the quotient curve equation after inserting the candidate Vélu coordinates. -/
@[expose] public def veluDeficit (S : Finset (F × F)) (r s : F) : F :=
  (W.veluY S r s) ^ 2 + W.a₁ * (W.veluX S r) * (W.veluY S r s) + W.a₃ * (W.veluY S r s)
    - ((W.veluX S r) ^ 3 + W.a₂ * (W.veluX S r) ^ 2
        + (W.veluQuotient S).a₄ * (W.veluX S r) + (W.veluQuotient S).a₆)

public theorem veluQuotient_equation_iff_veluDeficit_eq_zero (S : Finset (F × F)) (r s : F) :
    (W.veluQuotient S).toAffine.Equation (W.veluX S r) (W.veluY S r s)
      ↔ W.veluDeficit S r s = 0 := by
  rw [Affine.equation_iff, veluDeficit, veluQuotient_a₁, veluQuotient_a₂, veluQuotient_a₃,
    sub_eq_zero]

end Deficit
section Expansion

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_eq_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficit S r s
      = -(W.veluY S r s - s) * W.veluGy r s - (W.veluX S r - r) * W.veluGx r s
        + ((W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s)
            - (3 * r + W.a₂) * (W.veluX S r - r) ^ 2 - (W.veluX S r - r) ^ 3)
        + 5 * W.veluTSum S * W.veluX S r + W.b₂ * W.veluTSum S + 7 * W.veluWSum S := by
  rw [Affine.equation_iff] at hP
  simp only [veluDeficit, veluGx, veluGy, veluQuotient_a₄, veluQuotient_a₆]
  linear_combination hP

theorem veluDeficit_congr {S : Finset (F × F)} {r s r' s' : F}
    (hX : W.veluX S r = W.veluX S r') (hY : W.veluY S r s = W.veluY S r' s') :
    W.veluDeficit S r s = W.veluDeficit S r' s' := by
  unfold veluDeficit; rw [hX, hY]

end Expansion
section ConstancyCarrier

variable (F : Type*) [Field F] [DecidableEq F]

/-- For a cyclic kernel of order `p`, the candidate Vélu coordinates satisfy the quotient
equation away from the kernel's `x`-coordinates. -/
@[expose] public def VeluDeficitConstancyAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = 0

end ConstancyCarrier
end WeierstrassCurve
end
section

namespace WeierstrassCurve
section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem velu_orbitSumX_singleton_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluXNum x₀ y₀ x
      = (x - 2 * x₀) * (x - x₀) ^ 2
        + ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)
        + ((y - (-y₀ - W.a₁ * x₀ - W.a₃)) ^ 2
            + W.a₁ * (y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (x - x₀)
            - (W.a₂ + x + x₀) * (x - x₀) ^ 2) := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluXNum, veluT, veluU, veluGx, veluGy]
  linear_combination (-2 : R) * hP + 2 * hQ

theorem velu_orbitSumY_singleton_cleared {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluYNum x₀ y₀ x y
      = y * (x - x₀) ^ 3
        + (-(y - y₀) * (((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) - x * (x - x₀) ^ 2)
            - y * (x - x₀) ^ 3
            - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
            - W.a₃ * (x - x₀) ^ 3)
        + (-(y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (((y - (-y₀ - W.a₁ * x₀ - W.a₃)) ^ 2
              + W.a₁ * (y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) - x * (x - x₀) ^ 2)
            - y * (x - x₀) ^ 3
            - W.a₁ * ((y - (-y₀ - W.a₁ * x₀ - W.a₃)) ^ 2
              + W.a₁ * (y - (-y₀ - W.a₁ * x₀ - W.a₃)) * (x - x₀)
              - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀)
            - W.a₃ * (x - x₀) ^ 3)
        + (W.a₁ * x₀ + W.a₃) * (x - x₀) ^ 3 := by
  rw [Affine.equation_iff] at hP hQ
  simp only [veluYNum, veluT, veluU, veluGx, veluGy]
  linear_combination (2 * W.a₁ * x - W.a₁ * x₀ + W.a₃ + 2 * y) * hP
    + (-2 * W.a₁ * x + W.a₁ * x₀ - W.a₃ - 2 * y) * hQ

end CommRing
section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluX_singleton_eq_orbitSum [DecidableEq F] {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) (hx : x ≠ x₀) :
    W.veluX {(x₀, y₀)} x
      = x + W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀)
          + W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y (W.toAffine.negY x₀ y₀))
          - 2 * x₀ := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_orbitSumX_singleton_cleared hP hQ
  rw [W.veluX_singleton x₀ y₀ hx]
  simp only [Affine.slope_of_X_ne hx, Affine.addX, Affine.negY]
  field_simp
  linear_combination key

theorem veluY_singleton_eq_orbitSum [DecidableEq F] {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) (hx : x ≠ x₀) :
    W.veluY {(x₀, y₀)} x y
      = y + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀)
          + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y (W.toAffine.negY x₀ y₀))
          - y₀ - W.toAffine.negY x₀ y₀ := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have key := W.velu_orbitSumY_singleton_cleared hP hQ
  rw [W.veluY_singleton x₀ y₀ y hx]
  simp only [Affine.slope_of_X_ne hx, Affine.addY, Affine.negAddY, Affine.addX, Affine.negY]
  field_simp
  linear_combination key

end Field
end WeierstrassCurve
end
noncomputable section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

public theorem ord_sub_evalAt_pos (hrat : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  · exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        change f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

end Place
end AlgebraicCurve
end
section

noncomputable section

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_inv (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfi : f⁻¹ ≠ 0 := inv_ne_zero hf
  have hi : v.ord f⁻¹ = 0 := by rw [v.ord_inv, h, _root_.neg_zero]
  have hmul := v.evalAt_mul hv (v.mem_of_ord_nonneg hf h.ge) (v.mem_of_ord_nonneg hfi hi.ge)
  rw [mul_inv_cancel₀ hf, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

end Place
end AlgebraicCurve
end
section

section

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_add_eq_min {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f ≠ v.ord g) :
    v.ord (f + g) = min (v.ord f) (v.ord g) := by
  have hval : v.adicValuation f ≠ v.adicValuation g := by
    intro hcon
    exact h (by simp only [ord, hcon])
  have h1 : v.adicValuation (f + g) = max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add_of_distinct_val _ hval
  have hfg : f + g ≠ 0 := by
    intro hcon
    rw [hcon, _root_.map_zero] at h1
    rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, -⟩ | ⟨hmax, -⟩ <;>
      rw [hmax] at h1
    · exact v.adicValuation_ne_zero hf h1.symm
    · exact v.adicValuation_ne_zero hg h1.symm
  rcases max_cases (v.adicValuation f) (v.adicValuation g) with ⟨hmax, hle⟩ | ⟨hmax, hlt⟩ <;>
    rw [hmax] at h1
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hg)
      (v.adicValuation_ne_zero hf)).mpr hle
    have h2 : v.ord (f + g) = v.ord f := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega
  · have hlog := (WithZero.log_le_log (v.adicValuation_ne_zero hf)
      (v.adicValuation_ne_zero hg)).mpr hlt.le
    have h2 : v.ord (f + g) = v.ord g := by simp only [ord, h1]
    simp only [ord] at hlog h2 ⊢
    omega

public theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_ringHom_eq_natDegree_mul {φ : K[X] →+* F} (hφinj : Function.Injective φ)
    (hφC : ∀ c : K, φ (C c) = algebraMap K F c) (hz : v.ord (φ X) < 0) :
    ∀ {p : K[X]}, p ≠ 0 → v.ord (φ p) = p.natDegree * v.ord (φ X) := by
  have hX0 : φ X ≠ 0 := fun h => by simp [Place.ord, h] at hz
  have hmono : ∀ (c : K) (n : ℕ), c ≠ 0 → v.ord (φ (C c * X ^ n)) = n * v.ord (φ X) := by
    intro c n hc
    have hc0 : φ (C c) ≠ 0 := by
      rw [hφC]
      simpa using hc
    rw [map_mul, map_pow, v.ord_mul hc0 (pow_ne_zero n hX0), hφC, v.ord_algebraMap,
      v.ord_pow, zero_add]
  intro p
  induction hd : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    intro hp
    subst hd
    rcases eq_or_ne p.eraseLead 0 with he | he
    · conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow, he, zero_add]
      exact hmono _ _ (leadingCoeff_ne_zero.mpr hp)
    · have hlt : p.eraseLead.natDegree < p.natDegree := by
        rcases p.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h | h
        · exact h
        · exact absurd h he
      have hIH : v.ord (φ p.eraseLead) = p.eraseLead.natDegree * v.ord (φ X) :=
        ih _ hlt rfl he
      have hlead : v.ord (φ (C p.leadingCoeff * X ^ p.natDegree))
          = p.natDegree * v.ord (φ X) := hmono _ _ (leadingCoeff_ne_zero.mpr hp)
      have hcast : (p.eraseLead.natDegree : ℤ) < (p.natDegree : ℤ) := by exact_mod_cast hlt
      have hne : v.ord (φ p.eraseLead) ≠ v.ord (φ (C p.leadingCoeff * X ^ p.natDegree)) := by
        rw [hIH, hlead]
        nlinarith
      have he2 : φ (C p.leadingCoeff * X ^ p.natDegree) ≠ 0 := fun hcon =>
        mul_ne_zero (C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hp)) (pow_ne_zero _ X_ne_zero)
          (hφinj (hcon.trans (_root_.map_zero φ).symm))
      have he1 : φ p.eraseLead ≠ 0 := fun hcon => he (hφinj (hcon.trans (_root_.map_zero φ).symm))
      conv_lhs => rw [← p.eraseLead_add_C_mul_X_pow]
      rw [map_add, v.ord_add_eq_min he1 he2 hne, hIH, hlead]
      have h1 : (p.natDegree : ℤ) * v.ord (φ X) ≤ (p.eraseLead.natDegree : ℤ) * v.ord (φ X) := by
        nlinarith
      omega

theorem le_ord_ringHom_of_natDegree_le {φ : K[X] →+* F} (hφinj : Function.Injective φ)
    (hφC : ∀ c : K, φ (C c) = algebraMap K F c) (hz : v.ord (φ X) < 0)
    {p : K[X]} {d : ℕ} (hd : p.natDegree ≤ d) :
    (d : ℤ) * v.ord (φ X) ≤ v.ord (φ p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [_root_.map_zero, Place.ord_zero]
    nlinarith [hz]
  rw [v.ord_ringHom_eq_natDegree_mul hφinj hφC hz hp]
  have h1 : (p.natDegree : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  nlinarith

end Place
end AlgebraicCurve
namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

theorem natDegree_norm_smul_basis_left {p : F[X]} (hp : p ≠ 0) :
    ((Algebra.norm F[X] (p • (1 : W.CoordinateRing)
        + (0 : F[X]) • CoordinateRing.mk W Y)).natDegree : ℤ) = 2 * p.natDegree := by
  have hdeg := degree_norm_smul_basis (W' := W) p 0
  rw [Polynomial.degree_zero, show (2 : ℕ) • (⊥ : WithBot ℕ) + 3 = ⊥ by
      rw [two_nsmul]; simp, max_eq_left bot_le, Polynomial.degree_eq_natDegree hp, two_nsmul,
    ← Nat.cast_add] at hdeg
  rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  push_cast
  ring

theorem natDegree_norm_smul_basis_right {q : F[X]} (hq : q ≠ 0) :
    ((Algebra.norm F[X] ((0 : F[X]) • (1 : W.CoordinateRing)
        + q • CoordinateRing.mk W Y)).natDegree : ℤ) = 2 * q.natDegree + 3 := by
  have hdeg := degree_norm_smul_basis (W' := W) 0 q
  rw [Polynomial.degree_zero, show (2 : ℕ) • (⊥ : WithBot ℕ) = ⊥ by
      rw [two_nsmul]; simp, max_eq_right bot_le, Polynomial.degree_eq_natDegree hq, two_nsmul,
    ← Nat.cast_add, show ((3 : WithBot ℕ)) = ((3 : ℕ) : WithBot ℕ) from rfl,
    ← Nat.cast_add] at hdeg
  rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
  push_cast
  ring

theorem natDegree_norm_smul_basis_max {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    ((Algebra.norm F[X] (p • (1 : W.CoordinateRing)
        + q • CoordinateRing.mk W Y)).natDegree : ℤ)
      = max (2 * (p.natDegree : ℤ)) (2 * (q.natDegree : ℤ) + 3) := by
  have hdeg := degree_norm_smul_basis (W' := W) p q
  rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, two_nsmul,
    two_nsmul, ← Nat.cast_add, ← Nat.cast_add,
    show ((3 : WithBot ℕ)) = ((3 : ℕ) : WithBot ℕ) from rfl, ← Nat.cast_add] at hdeg
  rcases le_total (q.natDegree + q.natDegree + 3) (p.natDegree + p.natDegree) with h | h
  · rw [max_eq_left (by exact_mod_cast h)] at hdeg
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
    push_cast
    omega
  · rw [max_eq_right (by exact_mod_cast h)] at hdeg
    rw [Polynomial.natDegree_eq_of_degree_eq_some hdeg]
    push_cast
    omega

variable (v : AlgebraicCurve.Place F W.FunctionField)

theorem two_mul_ord_Y_eq_three_mul_ord_X (hv : ¬ IsFinitePlace v) :
    2 * v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
      = 3 * v.ord (polyToFunctionField W X) := by
  set η := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) with hηdef
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hη0 : η ≠ 0 := Y_image_ne_zero
  set c₁ : F[X] := C W.a₁ * X + C W.a₃ with hc₁def
  set cb : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ with hcbdef
  have hrel : η * η = polyToFunctionField W cb - polyToFunctionField W c₁ * η := by
    have h1 := smul_basis_mul_Y (W' := W) 0 1
    rw [zero_smul, zero_add, one_smul, one_mul, one_mul, zero_sub] at h1
    have h2 := congrArg (algebraMap W.CoordinateRing W.FunctionField) h1
    rw [map_mul, algebraMap_smul_basis, _root_.map_neg, neg_mul, ← sub_eq_add_neg] at h2
    exact h2
  have hrelL : (η + polyToFunctionField W c₁) * η = polyToFunctionField W cb := by
    rw [add_mul]
    linear_combination hrel
  have hcbdeg : cb.natDegree = 3 := by
    rw [hcbdef, ← one_mul (X ^ 3 : F[X]), ← C_1]
    exact Polynomial.natDegree_cubic one_ne_zero
  have hcb0 : cb ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hcbdeg
    exact absurd hcbdeg (by norm_num)
  have hcbord : v.ord (polyToFunctionField W cb) = 3 * v.ord (polyToFunctionField W X) := by
    rw [v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA
      hcb0, hcbdeg]
    push_cast
    ring
  have hc₁ord : (1 : ℤ) * v.ord (polyToFunctionField W X)
      ≤ v.ord (polyToFunctionField W c₁) := by
    refine v.le_ord_ringHom_of_natDegree_le polyToFunctionField_injective polyToFunctionField_C
      hA ?_
    rw [hc₁def]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff]
    refine ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp), by omega⟩
  rw [one_mul] at hc₁ord
  have hfac0 : η + polyToFunctionField W c₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrelL
    exact polyToFunctionField_ne_zero hcb0 hrelL.symm
  have hLHS : v.ord (η + polyToFunctionField W c₁) + v.ord η
      = 3 * v.ord (polyToFunctionField W X) := by
    rw [← hcbord, ← hrelL, v.ord_mul hfac0 hη0]
  rcases eq_or_ne (polyToFunctionField W c₁) 0 with hc₁0 | hc₁0
  · rw [hc₁0, add_zero] at hLHS
    omega
  · by_cases hBc : v.ord η = v.ord (polyToFunctionField W c₁)
    · exfalso
      have hmin : min (v.ord η) (v.ord (polyToFunctionField W c₁))
          ≤ v.ord (η + polyToFunctionField W c₁) := v.min_ord_le_ord_add' hfac0
      rw [← hBc, min_self] at hmin
      have hBA : v.ord (polyToFunctionField W X) ≤ v.ord η := hBc ▸ hc₁ord
      omega
    · have hsum : v.ord (η + polyToFunctionField W c₁)
          = min (v.ord η) (v.ord (polyToFunctionField W c₁)) :=
        v.ord_add_eq_min hη0 hc₁0 hBc
      rcases min_cases (v.ord η) (v.ord (polyToFunctionField W c₁)) with
        ⟨hm, hle⟩ | ⟨hm, hlt⟩ <;> rw [hm] at hsum
      · rw [hsum] at hLHS
        omega
      · exfalso
        rw [hsum] at hLHS
        omega

theorem ne_arith {A B s t : ℤ} (hA : A < 0) (hY : 2 * B = 3 * A) :
    s * A ≠ t * A + B := by
  intro hcon
  have h4 : (2 * s - (2 * t + 3)) * A = 0 := by linear_combination 2 * hcon + hY
  rcases mul_eq_zero.mp h4 with h5 | h5
  · omega
  · omega

theorem two_mul_min_arith {A B s t : ℤ} (hA : A < 0) (hY : 2 * B = 3 * A) :
    2 * min (s * A) (t * A + B) = A * max (2 * s) (2 * t + 3) := by
  rcases le_or_gt (2 * t + 3) (2 * s) with h | h
  · rw [max_eq_left h, min_eq_left (by nlinarith)]
    ring
  · rw [max_eq_right h.le, min_eq_right (by nlinarith)]
    linear_combination hY

theorem two_mul_ord_eq_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {f : W.CoordinateRing} (hf : f ≠ 0) :
    2 * v.ord (algebraMap W.CoordinateRing W.FunctionField f)
      = v.ord (polyToFunctionField W X) * ((Algebra.norm F[X] f).natDegree : ℤ) := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hη0 : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 :=
    Y_image_ne_zero
  have hYord := two_mul_ord_Y_eq_three_mul_ord_X v hv
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  by_cases hq : q = 0
  · subst hq
    have hp : p ≠ 0 := fun h => hf (by rw [h, zero_smul, zero_smul, add_zero])
    rw [natDegree_norm_smul_basis_left hp, algebraMap_smul_basis, _root_.map_zero, zero_mul,
      add_zero, v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C
      hA hp]
    ring
  · by_cases hp : p = 0
    · subst hp
      rw [natDegree_norm_smul_basis_right hq, algebraMap_smul_basis, _root_.map_zero, zero_add,
        v.ord_mul (polyToFunctionField_ne_zero hq) hη0,
        v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hq]
      linear_combination hYord
    · rw [natDegree_norm_smul_basis_max hp hq, algebraMap_smul_basis]
      have hordp : v.ord (polyToFunctionField W p)
          = (p.natDegree : ℤ) * v.ord (polyToFunctionField W X) :=
        v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA hp
      have hordqy : v.ord (polyToFunctionField W q
            * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
          = (q.natDegree : ℤ) * v.ord (polyToFunctionField W X)
            + v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        rw [v.ord_mul (polyToFunctionField_ne_zero hq) hη0,
          v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C hA
            hq]
      have hne : v.ord (polyToFunctionField W p) ≠ v.ord (polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        rw [hordp, hordqy]
        exact ne_arith hA hYord
      have hqy0 : polyToFunctionField W q
          * algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) ≠ 0 :=
        mul_ne_zero (polyToFunctionField_ne_zero hq) hη0
      rw [v.ord_add_eq_min (polyToFunctionField_ne_zero hp) hqy0 hne, hordp, hordqy]
      exact two_mul_min_arith hA hYord

theorem ord_X_eq_neg_two_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (polyToFunctionField W X) = -2 := by
  have hA : v.ord (polyToFunctionField W X) < 0 := ord_X_neg_of_not_isFinitePlace v hv
  have hYord := two_mul_ord_Y_eq_three_mul_ord_X v hv
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπord : v.ord (π : W.FunctionField) = 1 := v.ord_coe_irreducible hπ
  have hπ0 : (π : W.FunctionField) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing)
    (π : W.FunctionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, _root_.map_zero, zero_div] at hab
    exact hπ0 hab.symm
  have ha' : algebraMap W.CoordinateRing W.FunctionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr ha0
  have hb' : algebraMap W.CoordinateRing W.FunctionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W.CoordinateRing W.FunctionField)).mpr hb0
  have h1 := two_mul_ord_eq_of_not_isFinitePlace v hv ha0
  have h2 := two_mul_ord_eq_of_not_isFinitePlace v hv hb0
  have h3 : v.ord (π : W.FunctionField)
      = v.ord (algebraMap W.CoordinateRing W.FunctionField a)
        - v.ord (algebraMap W.CoordinateRing W.FunctionField b) := by
    rw [← hab, div_eq_mul_inv, v.ord_mul ha' (inv_ne_zero hb'), v.ord_inv]
    ring
  rw [hπord] at h3
  have h4 : (2 : ℤ) = v.ord (polyToFunctionField W X) * (((Algebra.norm F[X] a).natDegree : ℤ)
      - ((Algebra.norm F[X] b).natDegree : ℤ)) := by
    linear_combination 2 * h3 + h1 - h2
  have h5 : v.ord (polyToFunctionField W X) ∣ 2 := ⟨_, h4⟩
  have h6 : (2 : ℤ) ∣ v.ord (polyToFunctionField W X) := by
    have h7 : (2 : ℤ) ∣ 3 * v.ord (polyToFunctionField W X) := ⟨_, hYord.symm⟩
    omega
  have h8 : (v.ord (polyToFunctionField W X)).natAbs ∣ (2 : ℤ).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h5
  have h9 : (2 : ℤ).natAbs ∣ (v.ord (polyToFunctionField W X)).natAbs :=
    Int.natAbs_dvd_natAbs.mpr h6
  have h10 : (v.ord (polyToFunctionField W X)).natAbs = 2 :=
    Nat.dvd_antisymm (by simpa using h8) (by simpa using h9)
  omega

theorem ord_Y_eq_neg_three_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) = -3 := by
  have h1 := two_mul_ord_Y_eq_three_mul_ord_X v hv
  rw [ord_X_eq_neg_two_of_not_isFinitePlace v hv] at h1
  omega

end Affine
end WeierstrassCurve
end
section

section

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem Place.ord_div (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f / g) = v.ord f - v.ord g := by
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hg), v.ord_inv]
  ring

end AlgebraicCurve
namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

public theorem mk_mem_XYIdeal_iff {x y : F} (h : W.Equation x y) (P : F[X][Y]) :
    CoordinateRing.mk W P ∈ XYIdeal W x (C y) ↔ P.evalEval x y = 0 := by
  have hmap : XYIdeal W x (C y)
      = Ideal.map (CoordinateRing.mk W) (Ideal.span {C (X - C x), Y - C (C y)}) := by
    rw [Ideal.map_span, Set.image_pair]
    rfl
  rw [hmap]
  constructor
  · intro hP
    obtain ⟨Q, hQ, hQP⟩ := (Ideal.mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective).mp hP
    obtain ⟨c, hc⟩ := AdjoinRoot.mk_eq_mk.mp hQP
    have hQ0 : Q.evalEval x y = 0 :=
      mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mp hQ
    have hW0 : W.polynomial.evalEval x y = 0 := h
    have hPQ : P = Q - W.polynomial * c := by rw [← hc]; ring
    rw [hPQ]
    simp only [evalEval, eval_sub, eval_mul] at hQ0 hW0 ⊢
    rw [hQ0, hW0, zero_mul, sub_zero]
  · intro hP
    exact Ideal.mem_map_of_mem _ (mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr hP)

end Affine
end WeierstrassCurve
end
section

noncomputable section

namespace WeierstrassCurve
section PsiEval

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

lemma eval_Ψ₃_eq_b' (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp only [Ψ₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat]

end PsiEval
section LinearTerm

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitLinearTerm (x₀ y₀ r s : F) : F :=
  -(W.veluY {(x₀, y₀)} r s - s) * W.veluGy r s
    - (W.veluX {(x₀, y₀)} r - r) * W.veluGx r s
    + 5 * W.veluT x₀ y₀ * r + W.b₂ * W.veluT x₀ y₀ + 7 * W.veluW x₀ y₀

end LinearTerm
section ClearedIdentity

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem veluDeficitLinearTerm_mul_cube_eq {x₀ y₀ r s : R}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) :
    -(W.veluU x₀ y₀ * W.veluGy r s
        - W.veluT x₀ y₀ * (W.a₁ * (r - x₀) + s - y₀) * (r - x₀)
        - (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (r - x₀)) * W.veluGy r s
      - (W.veluT x₀ y₀ * (r - x₀) + W.veluU x₀ y₀) * W.veluGx r s * (r - x₀)
      + (5 * W.veluT x₀ y₀ * r + W.b₂ * W.veluT x₀ y₀ + 7 * W.veluW x₀ y₀) * (r - x₀) ^ 3
      = -(W.veluU x₀ y₀) ^ 2 - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ * (r - x₀)
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) * (r - x₀) ^ 2 := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq_b']
  simp only [veluT, veluU, veluW, veluGx, veluGy, b₂, b₄, b₆, b₈]
  linear_combination
    (-2*W.a₁ ^ 2*r*x₀ - 2*W.a₁ ^ 2*x₀ ^ 2 - 2*W.a₁*W.a₃*r - 6*W.a₁*W.a₃*x₀ - 16*W.a₁*x₀*y₀
        - 8*W.a₂*r*x₀ + 8*W.a₂*x₀ ^ 2 - 4*W.a₃ ^ 2 - 16*W.a₃*y₀ - 4*W.a₄*r + 4*W.a₄*x₀
        - 12*r*x₀ ^ 2 + 12*x₀ ^ 3 - 16*y₀ ^ 2) * hP
    + (-6*W.a₁ ^ 2*r ^ 2 + 14*W.a₁ ^ 2*r*x₀ - 4*W.a₁ ^ 2*x₀ ^ 2 + 2*W.a₁*W.a₃*r + 6*W.a₁*W.a₃*x₀
        + 16*W.a₁*x₀*y₀ - 24*W.a₂*r ^ 2 + 56*W.a₂*r*x₀ - 32*W.a₂*x₀ ^ 2 + 4*W.a₃ ^ 2 + 16*W.a₃*y₀
        + 4*W.a₄*r - 4*W.a₄*x₀ - 72*r ^ 2*x₀ + 156*r*x₀ ^ 2 - 84*x₀ ^ 3 + 16*y₀ ^ 2) * hQ

end ClearedIdentity
section FieldLaurent

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma veluDeficitLinearTerm_mul_cube {x₀ y₀ r s : F} (hr : r ≠ x₀) :
    W.veluDeficitLinearTerm x₀ y₀ r s * (r - x₀) ^ 3
      = -(W.veluU x₀ y₀ * W.veluGy r s
          - W.veluT x₀ y₀ * (W.a₁ * (r - x₀) + s - y₀) * (r - x₀)
          - (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (r - x₀)) * W.veluGy r s
        - (W.veluT x₀ y₀ * (r - x₀) + W.veluU x₀ y₀) * W.veluGx r s * (r - x₀)
        + (5 * W.veluT x₀ y₀ * r + W.b₂ * W.veluT x₀ y₀ + 7 * W.veluW x₀ y₀) * (r - x₀) ^ 3 := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  unfold veluDeficitLinearTerm
  simp only [veluX, veluY, veluGy, Finset.sum_singleton]
  field_simp
  ring

theorem veluDeficitLinearTerm_eq {x₀ y₀ r s : F}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) (hr : r ≠ x₀) :
    W.veluDeficitLinearTerm x₀ y₀ r s
      = -(W.veluU x₀ y₀) ^ 2 / (r - x₀) ^ 3
        - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ / (r - x₀) ^ 2
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) / (r - x₀) := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  have hd3 : (r - x₀) ^ 3 ≠ 0 := pow_ne_zero 3 hd
  have hLHS := W.veluDeficitLinearTerm_mul_cube (x₀ := x₀) (y₀ := y₀) (s := s) hr
  have key := W.veluDeficitLinearTerm_mul_cube_eq hP hQ
  have hRHS : (-(W.veluU x₀ y₀) ^ 2 / (r - x₀) ^ 3
        - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ / (r - x₀) ^ 2
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) / (r - x₀)) * (r - x₀) ^ 3
      = -(W.veluU x₀ y₀) ^ 2 - 3 * W.veluT x₀ y₀ * W.veluU x₀ y₀ * (r - x₀)
        - (3 * (W.veluT x₀ y₀) ^ 2 + 6 * (W.Ψ₃).eval x₀) * (r - x₀) ^ 2 := by
    have hd2 : (r - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hd3,
      show (r - x₀) ^ 3 = (r - x₀) ^ 2 * (r - x₀) from by ring, ← mul_assoc,
      div_mul_cancel₀ _ hd2, show (r - x₀) ^ 2 * (r - x₀) = (r - x₀) * (r - x₀) ^ 2 from by ring,
      ← mul_assoc, div_mul_cancel₀ _ hd]
  exact mul_right_cancel₀ hd3 (by rw [hLHS, key, ← hRHS])

end FieldLaurent
section SumDecomposition

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_linearPart_eq_sum (S : Finset (F × F)) (r s : F) :
    -(W.veluY S r s - s) * W.veluGy r s - (W.veluX S r - r) * W.veluGx r s
        + 5 * W.veluTSum S * r + W.b₂ * W.veluTSum S + 7 * W.veluWSum S
      = ∑ Q ∈ S, W.veluDeficitLinearTerm Q.1 Q.2 r s := by
  simp only [veluDeficitLinearTerm, veluX, veluY, veluTSum, veluWSum, Finset.sum_singleton,
    add_sub_cancel_left, sub_sub_cancel_left, neg_neg, Finset.sum_mul, Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun Q _ => by ring

end SumDecomposition
section FullExpansion

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitBracket (S : Finset (F × F)) (r s : F) : F :=
  ((W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s)
      - (3 * r + W.a₂) * (W.veluX S r - r) ^ 2 - (W.veluX S r - r) ^ 3)
    + 5 * W.veluTSum S * (W.veluX S r - r)

theorem veluDeficit_eq_laurentSum_add_bracket {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (hr : ∀ A ∈ S, r ≠ A.1) :
    W.veluDeficit S r s
      = (∑ Q ∈ S, (-(W.veluU Q.1 Q.2) ^ 2 / (r - Q.1) ^ 3
          - 3 * W.veluT Q.1 Q.2 * W.veluU Q.1 Q.2 / (r - Q.1) ^ 2
          - (3 * (W.veluT Q.1 Q.2) ^ 2 + 6 * (W.Ψ₃).eval Q.1) / (r - Q.1)))
        + W.veluDeficitBracket S r s := by
  have hsum : ∑ Q ∈ S, W.veluDeficitLinearTerm Q.1 Q.2 r s
      = ∑ Q ∈ S, (-(W.veluU Q.1 Q.2) ^ 2 / (r - Q.1) ^ 3
          - 3 * W.veluT Q.1 Q.2 * W.veluU Q.1 Q.2 / (r - Q.1) ^ 2
          - (3 * (W.veluT Q.1 Q.2) ^ 2 + 6 * (W.Ψ₃).eval Q.1) / (r - Q.1)) :=
    Finset.sum_congr rfl fun Q hQmem =>
      W.veluDeficitLinearTerm_eq hP (hSeq Q hQmem) (hr Q hQmem)
  rw [← hsum, ← W.veluDeficit_linearPart_eq_sum, W.veluDeficit_eq_of_equation hP,
    veluDeficitBracket]
  ring

end FullExpansion
end WeierstrassCurve
end
section

noncomputable section

namespace WeierstrassCurve
section PsiCofactor

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluDeficitPsiCofactor (x₀ x : R) : R :=
  2*W.a₁ ^ 2*x ^ 3*x₀ - 3*W.a₁ ^ 2*x ^ 2*x₀ ^ 2 + W.a₁ ^ 2*x₀ ^ 4 + 2*W.a₁*W.a₃*x ^ 3
    - 6*W.a₁*W.a₃*x*x₀ ^ 2 + 4*W.a₁*W.a₃*x₀ ^ 3 + 8*W.a₂*x ^ 3*x₀ - 12*W.a₂*x ^ 2*x₀ ^ 2
    + 4*W.a₂*x₀ ^ 4 + 3*W.a₃ ^ 2*x ^ 2 - 6*W.a₃ ^ 2*x*x₀ + 3*W.a₃ ^ 2*x₀ ^ 2 + 4*W.a₄*x ^ 3
    - 12*W.a₄*x*x₀ ^ 2 + 8*W.a₄*x₀ ^ 3 + 12*W.a₆*x ^ 2 - 24*W.a₆*x*x₀ + 12*W.a₆*x₀ ^ 2 - 6*x ^ 5
    + 30*x ^ 4*x₀ - 48*x ^ 3*x₀ ^ 2 + 36*x ^ 2*x₀ ^ 3 - 18*x*x₀ ^ 4 + 6*x₀ ^ 5

lemma eval_Ψ₃_eq' (x : R) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  rw [Ψ₃]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow, eval_ofNat]

theorem velu_singleton_deficit_cleared_eq_psi {x₀ y₀ x y : R}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀) :
    W.veluYNum x₀ y₀ x y ^ 2 + W.a₁ * W.veluXNum x₀ y₀ x * W.veluYNum x₀ y₀ x y * (x - x₀)
        + W.a₃ * W.veluYNum x₀ y₀ x y * (x - x₀) ^ 3
      - (W.veluXNum x₀ y₀ x ^ 3 + W.a₂ * W.veluXNum x₀ y₀ x ^ 2 * (x - x₀) ^ 2
        + (W.a₄ - 5 * W.veluT x₀ y₀) * W.veluXNum x₀ y₀ x * (x - x₀) ^ 4
        + (W.a₆ - W.b₂ * W.veluT x₀ y₀ - 7 * W.veluW x₀ y₀) * (x - x₀) ^ 6)
      = W.veluDeficitPsiCofactor x₀ x * (W.Ψ₃).eval x₀ := by
  rw [Affine.equation_iff] at hP hQ
  rw [W.eval_Ψ₃_eq']
  simp only [veluDeficitPsiCofactor, b₂, b₄, b₆, b₈, veluXNum, veluYNum, veluT, veluU, veluW,
    veluGx, veluGy]
  linear_combination
    (W.a₁ ^ 4*x ^ 2*x₀ ^ 2 + 2*W.a₁ ^ 4*x*x₀ ^ 3 + W.a₁ ^ 4*x₀ ^ 4 + 2*W.a₁ ^ 3*W.a₃*x ^ 2*x₀
      + 8*W.a₁ ^ 3*W.a₃*x*x₀ ^ 2 + 6*W.a₁ ^ 3*W.a₃*x₀ ^ 3 + 16*W.a₁ ^ 3*x*x₀ ^ 2*y₀
      + 16*W.a₁ ^ 3*x₀ ^ 3*y₀ + 8*W.a₁ ^ 2*W.a₂*x ^ 2*x₀ ^ 2 - 8*W.a₁ ^ 2*W.a₂*x₀ ^ 4
      + W.a₁ ^ 2*W.a₃ ^ 2*x ^ 2 + 10*W.a₁ ^ 2*W.a₃ ^ 2*x*x₀ + 13*W.a₁ ^ 2*W.a₃ ^ 2*x₀ ^ 2
      + 32*W.a₁ ^ 2*W.a₃*x*x₀*y₀ + 64*W.a₁ ^ 2*W.a₃*x₀ ^ 2*y₀ + 4*W.a₁ ^ 2*W.a₄*x ^ 2*x₀
      - 4*W.a₁ ^ 2*W.a₄*x₀ ^ 3 - 2*W.a₁ ^ 2*x ^ 4*x₀ + 4*W.a₁ ^ 2*x ^ 3*x₀ ^ 2
      + 12*W.a₁ ^ 2*x ^ 2*x₀ ^ 3 - 4*W.a₁ ^ 2*x*x₀ ^ 4 + 16*W.a₁ ^ 2*x*x₀*y₀ ^ 2
      - 10*W.a₁ ^ 2*x₀ ^ 5 + 80*W.a₁ ^ 2*x₀ ^ 2*y₀ ^ 2 + 8*W.a₁*W.a₂*W.a₃*x ^ 2*x₀
      + 16*W.a₁*W.a₂*W.a₃*x*x₀ ^ 2 - 24*W.a₁*W.a₂*W.a₃*x₀ ^ 3 + 64*W.a₁*W.a₂*x*x₀ ^ 2*y₀
      - 64*W.a₁*W.a₂*x₀ ^ 3*y₀ + 4*W.a₁*W.a₃ ^ 3*x + 12*W.a₁*W.a₃ ^ 3*x₀ + 16*W.a₁*W.a₃ ^ 2*x*y₀
      + 80*W.a₁*W.a₃ ^ 2*x₀*y₀ + 4*W.a₁*W.a₃*W.a₄*x ^ 2 + 8*W.a₁*W.a₃*W.a₄*x*x₀
      - 12*W.a₁*W.a₃*W.a₄*x₀ ^ 2 - 2*W.a₁*W.a₃*x ^ 4 + 24*W.a₁*W.a₃*x ^ 2*x₀ ^ 2
      + 8*W.a₁*W.a₃*x*x₀ ^ 3 + 16*W.a₁*W.a₃*x*y₀ ^ 2 - 30*W.a₁*W.a₃*x₀ ^ 4
      + 176*W.a₁*W.a₃*x₀*y₀ ^ 2 + 32*W.a₁*W.a₄*x*x₀*y₀ - 32*W.a₁*W.a₄*x₀ ^ 2*y₀
      - 16*W.a₁*x ^ 3*x₀*y₀ + 48*W.a₁*x ^ 2*x₀ ^ 2*y₀ + 48*W.a₁*x*x₀ ^ 3*y₀ - 80*W.a₁*x₀ ^ 4*y₀
      + 128*W.a₁*x₀*y₀ ^ 3 + 16*W.a₂ ^ 2*x ^ 2*x₀ ^ 2 - 32*W.a₂ ^ 2*x*x₀ ^ 3 + 16*W.a₂ ^ 2*x₀ ^ 4
      + 16*W.a₂*W.a₃ ^ 2*x*x₀ - 16*W.a₂*W.a₃ ^ 2*x₀ ^ 2 + 64*W.a₂*W.a₃*x*x₀*y₀
      - 64*W.a₂*W.a₃*x₀ ^ 2*y₀ + 16*W.a₂*W.a₄*x ^ 2*x₀ - 32*W.a₂*W.a₄*x*x₀ ^ 2
      + 16*W.a₂*W.a₄*x₀ ^ 3 - 8*W.a₂*x ^ 4*x₀ + 32*W.a₂*x ^ 3*x₀ ^ 2 - 64*W.a₂*x*x₀ ^ 4
      + 64*W.a₂*x*x₀*y₀ ^ 2 + 40*W.a₂*x₀ ^ 5 - 64*W.a₂*x₀ ^ 2*y₀ ^ 2 + 4*W.a₃ ^ 4 + 32*W.a₃ ^ 3*y₀
      + 8*W.a₃ ^ 2*W.a₄*x - 8*W.a₃ ^ 2*W.a₄*x₀ - 4*W.a₃ ^ 2*x ^ 3 + 12*W.a₃ ^ 2*x ^ 2*x₀
      + 12*W.a₃ ^ 2*x*x₀ ^ 2 - 20*W.a₃ ^ 2*x₀ ^ 3 + 96*W.a₃ ^ 2*y₀ ^ 2 + 32*W.a₃*W.a₄*x*y₀
      - 32*W.a₃*W.a₄*x₀*y₀ - 16*W.a₃*x ^ 3*y₀ + 48*W.a₃*x ^ 2*x₀*y₀ + 48*W.a₃*x*x₀ ^ 2*y₀
      - 80*W.a₃*x₀ ^ 3*y₀ + 128*W.a₃*y₀ ^ 3 + 4*W.a₄ ^ 2*x ^ 2 - 8*W.a₄ ^ 2*x*x₀
      + 4*W.a₄ ^ 2*x₀ ^ 2 - 4*W.a₄*x ^ 4 + 16*W.a₄*x ^ 3*x₀ - 32*W.a₄*x*x₀ ^ 3 + 32*W.a₄*x*y₀ ^ 2
      + 20*W.a₄*x₀ ^ 4 - 32*W.a₄*x₀*y₀ ^ 2 + x ^ 6 - 6*x ^ 5*x₀ + 3*x ^ 4*x₀ ^ 2 + 28*x ^ 3*x₀ ^ 3
      - 16*x ^ 3*y₀ ^ 2 - 21*x ^ 2*x₀ ^ 4 + 48*x ^ 2*x₀*y₀ ^ 2 - 30*x*x₀ ^ 5 + 48*x*x₀ ^ 2*y₀ ^ 2
      + 25*x₀ ^ 6 - 80*x₀ ^ 3*y₀ ^ 2 + 64*y₀ ^ 4) * hP
    + (2*W.a₁ ^ 4*x ^ 3*x₀ - 4*W.a₁ ^ 4*x ^ 2*x₀ ^ 2 - 2*W.a₁ ^ 4*x*x₀ ^ 3 + 2*W.a₁ ^ 3*W.a₃*x ^ 3
      - 2*W.a₁ ^ 3*W.a₃*x ^ 2*x₀ - 14*W.a₁ ^ 3*W.a₃*x*x₀ ^ 2 - 2*W.a₁ ^ 3*W.a₃*x₀ ^ 3
      + 12*W.a₁ ^ 3*x ^ 2*x₀*y₀ - 40*W.a₁ ^ 3*x*x₀ ^ 2*y₀ - 4*W.a₁ ^ 3*x₀ ^ 3*y₀
      + 16*W.a₁ ^ 2*W.a₂*x ^ 3*x₀ - 44*W.a₁ ^ 2*W.a₂*x ^ 2*x₀ ^ 2 + 24*W.a₁ ^ 2*W.a₂*x*x₀ ^ 3
      + 4*W.a₁ ^ 2*W.a₂*x₀ ^ 4 + 2*W.a₁ ^ 2*W.a₃ ^ 2*x ^ 2 - 16*W.a₁ ^ 2*W.a₃ ^ 2*x*x₀
      - 10*W.a₁ ^ 2*W.a₃ ^ 2*x₀ ^ 2 + 12*W.a₁ ^ 2*W.a₃*x ^ 2*y₀ - 56*W.a₁ ^ 2*W.a₃*x*x₀*y₀
      - 52*W.a₁ ^ 2*W.a₃*x₀ ^ 2*y₀ + 4*W.a₁ ^ 2*W.a₄*x ^ 3 - 16*W.a₁ ^ 2*W.a₄*x ^ 2*x₀
      + 12*W.a₁ ^ 2*W.a₄*x*x₀ ^ 2 + 12*W.a₁ ^ 2*W.a₆*x ^ 2 - 24*W.a₁ ^ 2*W.a₆*x*x₀
      + 12*W.a₁ ^ 2*W.a₆*x₀ ^ 2 - 6*W.a₁ ^ 2*x ^ 5 + 32*W.a₁ ^ 2*x ^ 4*x₀
      - 28*W.a₁ ^ 2*x ^ 3*x₀ ^ 2 - 12*W.a₁ ^ 2*x ^ 2*x₀ ^ 3 + 12*W.a₁ ^ 2*x ^ 2*y₀ ^ 2
      - 14*W.a₁ ^ 2*x*x₀ ^ 4 - 40*W.a₁ ^ 2*x*x₀*y₀ ^ 2 + 28*W.a₁ ^ 2*x₀ ^ 5
      - 68*W.a₁ ^ 2*x₀ ^ 2*y₀ ^ 2 + 8*W.a₁*W.a₂*W.a₃*x ^ 3 - 8*W.a₁*W.a₂*W.a₃*x ^ 2*x₀
      - 40*W.a₁*W.a₂*W.a₃*x*x₀ ^ 2 + 40*W.a₁*W.a₂*W.a₃*x₀ ^ 3 + 48*W.a₁*W.a₂*x ^ 2*x₀*y₀
      - 160*W.a₁*W.a₂*x*x₀ ^ 2*y₀ + 112*W.a₁*W.a₂*x₀ ^ 3*y₀ - 4*W.a₁*W.a₃ ^ 3*x
      - 12*W.a₁*W.a₃ ^ 3*x₀ - 16*W.a₁*W.a₃ ^ 2*x*y₀ - 80*W.a₁*W.a₃ ^ 2*x₀*y₀
      - 16*W.a₁*W.a₃*W.a₄*x ^ 2 + 16*W.a₁*W.a₃*W.a₄*x*x₀ + 2*W.a₁*W.a₃*x ^ 4 + 24*W.a₁*W.a₃*x ^ 3*x₀
      + 12*W.a₁*W.a₃*x ^ 2*x₀ ^ 2 - 152*W.a₁*W.a₃*x*x₀ ^ 3 - 16*W.a₁*W.a₃*x*y₀ ^ 2
      + 114*W.a₁*W.a₃*x₀ ^ 4 - 176*W.a₁*W.a₃*x₀*y₀ ^ 2 - 32*W.a₁*W.a₄*x*x₀*y₀
      + 32*W.a₁*W.a₄*x₀ ^ 2*y₀ + 16*W.a₁*x ^ 3*x₀*y₀ + 96*W.a₁*x ^ 2*x₀ ^ 2*y₀
      - 336*W.a₁*x*x₀ ^ 3*y₀ + 224*W.a₁*x₀ ^ 4*y₀ - 128*W.a₁*x₀*y₀ ^ 3 + 32*W.a₂ ^ 2*x ^ 3*x₀
      - 112*W.a₂ ^ 2*x ^ 2*x₀ ^ 2 + 128*W.a₂ ^ 2*x*x₀ ^ 3 - 48*W.a₂ ^ 2*x₀ ^ 4
      + 24*W.a₂*W.a₃ ^ 2*x ^ 2 - 64*W.a₂*W.a₃ ^ 2*x*x₀ + 40*W.a₂*W.a₃ ^ 2*x₀ ^ 2
      + 48*W.a₂*W.a₃*x ^ 2*y₀ - 160*W.a₂*W.a₃*x*x₀*y₀ + 112*W.a₂*W.a₃*x₀ ^ 2*y₀ + 16*W.a₂*W.a₄*x ^ 3
      - 64*W.a₂*W.a₄*x ^ 2*x₀ + 80*W.a₂*W.a₄*x*x₀ ^ 2 - 32*W.a₂*W.a₄*x₀ ^ 3 + 48*W.a₂*W.a₆*x ^ 2
      - 96*W.a₂*W.a₆*x*x₀ + 48*W.a₂*W.a₆*x₀ ^ 2 - 24*W.a₂*x ^ 5 + 128*W.a₂*x ^ 4*x₀
      - 128*W.a₂*x ^ 3*x₀ ^ 2 - 144*W.a₂*x ^ 2*x₀ ^ 3 + 48*W.a₂*x ^ 2*y₀ ^ 2 + 280*W.a₂*x*x₀ ^ 4
      - 160*W.a₂*x*x₀*y₀ ^ 2 - 112*W.a₂*x₀ ^ 5 + 112*W.a₂*x₀ ^ 2*y₀ ^ 2 - 4*W.a₃ ^ 4
      - 32*W.a₃ ^ 3*y₀ - 8*W.a₃ ^ 2*W.a₄*x + 8*W.a₃ ^ 2*W.a₄*x₀ + 4*W.a₃ ^ 2*x ^ 3
      + 60*W.a₃ ^ 2*x ^ 2*x₀ - 156*W.a₃ ^ 2*x*x₀ ^ 2 + 92*W.a₃ ^ 2*x₀ ^ 3 - 96*W.a₃ ^ 2*y₀ ^ 2
      - 32*W.a₃*W.a₄*x*y₀ + 32*W.a₃*W.a₄*x₀*y₀ + 16*W.a₃*x ^ 3*y₀ + 96*W.a₃*x ^ 2*x₀*y₀
      - 336*W.a₃*x*x₀ ^ 2*y₀ + 224*W.a₃*x₀ ^ 3*y₀ - 128*W.a₃*y₀ ^ 3 - 16*W.a₄ ^ 2*x ^ 2
      + 32*W.a₄ ^ 2*x*x₀ - 16*W.a₄ ^ 2*x₀ ^ 2 + 4*W.a₄*x ^ 4 + 32*W.a₄*x ^ 3*x₀
      - 72*W.a₄*x ^ 2*x₀ ^ 2 + 32*W.a₄*x*x₀ ^ 3 - 32*W.a₄*x*y₀ ^ 2 + 4*W.a₄*x₀ ^ 4
      + 32*W.a₄*x₀*y₀ ^ 2 + 144*W.a₆*x ^ 2*x₀ - 288*W.a₆*x*x₀ ^ 2 + 144*W.a₆*x₀ ^ 3 - 72*x ^ 5*x₀
      + 372*x ^ 4*x₀ ^ 2 - 624*x ^ 3*x₀ ^ 3 + 16*x ^ 3*y₀ ^ 2 + 360*x ^ 2*x₀ ^ 4
      + 96*x ^ 2*x₀*y₀ ^ 2 + 24*x*x₀ ^ 5 - 336*x*x₀ ^ 2*y₀ ^ 2 - 60*x₀ ^ 6 + 224*x₀ ^ 3*y₀ ^ 2
      - 64*y₀ ^ 4) * hQ

end PsiCofactor
section PsiField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_singleton_mul_pow_eq_psi {x₀ y₀ r s : F}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) (hr : r ≠ x₀) :
    W.veluDeficit {(x₀, y₀)} r s * (r - x₀) ^ 6
      = W.veluDeficitPsiCofactor x₀ r * (W.Ψ₃).eval x₀ := by
  have hd : r - x₀ ≠ 0 := sub_ne_zero.mpr hr
  rw [← W.velu_singleton_deficit_cleared_eq_psi hP hQ, veluDeficit,
    W.veluX_singleton x₀ y₀ hr, W.veluY_singleton x₀ y₀ s hr, veluQuotient_a₄, veluQuotient_a₆,
    veluTSum, veluWSum, Finset.sum_singleton, Finset.sum_singleton]
  field_simp

end PsiField
section LinQuad

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def veluDeficitLin (S : Finset (F × F)) (r s : F) : F :=
  -(W.veluY S r s - s) * W.veluGy r s - (W.veluX S r - r) * W.veluGx r s
    + 5 * W.veluTSum S * r + W.b₂ * W.veluTSum S + 7 * W.veluWSum S

/-- The nonlinear part of the equation residual in the Vélu coordinate corrections. -/
@[expose] public def veluDeficitQuad (S : Finset (F × F)) (r s : F) : F :=
  (W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s)
    - (3 * r + W.a₂) * (W.veluX S r - r) ^ 2 - (W.veluX S r - r) ^ 3
    + 5 * W.veluTSum S * (W.veluX S r - r)

theorem veluDeficit_eq_lin_add_quad_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficit S r s = W.veluDeficitLin S r s + W.veluDeficitQuad S r s := by
  rw [W.veluDeficit_eq_of_equation hP, veluDeficitLin, veluDeficitQuad]
  ring

@[scoped simp] lemma veluDeficitLin_empty (r s : F) : W.veluDeficitLin ∅ r s = 0 := by
  simp [veluDeficitLin]

theorem veluDeficitLin_eq_sum_singleton (S : Finset (F × F)) (r s : F) :
    W.veluDeficitLin S r s = ∑ A ∈ S, W.veluDeficitLin {A} r s := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert A S hA ih =>
    rw [Finset.sum_insert hA, ← ih]
    simp only [veluDeficitLin, veluTSum, veluWSum, veluX, veluY, Finset.sum_insert hA,
      Finset.sum_singleton]
    ring

end LinQuad
section SumDecomp

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The nonlinear residual for the whole summing set minus the sum of the singleton nonlinear
residuals. -/
@[expose] public def veluDeficitCrossQuad (S : Finset (F × F)) (r s : F) : F :=
  W.veluDeficitQuad S r s - ∑ A ∈ S, W.veluDeficitQuad {A} r s

theorem veluDeficit_eq_sum_singleton_add_crossQuad {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficit S r s
      = (∑ A ∈ S, W.veluDeficit {A} r s) + W.veluDeficitCrossQuad S r s := by
  rw [W.veluDeficit_eq_lin_add_quad_of_equation hP, veluDeficitCrossQuad,
    W.veluDeficitLin_eq_sum_singleton,
    show (∑ A ∈ S, W.veluDeficit {A} r s)
        = ∑ A ∈ S, (W.veluDeficitLin {A} r s + W.veluDeficitQuad {A} r s) from
      Finset.sum_congr rfl fun A _ => W.veluDeficit_eq_lin_add_quad_of_equation hP,
    Finset.sum_add_distrib]
  ring

end SumDecomp
end WeierstrassCurve
end

noncomputable section

namespace WeierstrassCurve
section GeneralOrbitSum

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem veluY_eq_add_sum_singleton (S : Finset (F × F)) (x y : F) :
    W.veluY S x y = y + ∑ P ∈ S, (W.veluY {P} x y - y) := by
  simp only [veluY, Finset.sum_singleton, sub_sub_cancel_left, Finset.sum_neg_distrib]
  ring

theorem veluY_eq_orbitSum_fieldRed {S : Finset (F × F)} {x y : F} (hP : W.toAffine.Equation x y)
    (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2) (hx : ∀ A ∈ S, x ≠ A.1) :
    W.veluY S x y = y + ∑ A ∈ S,
      (W.toAffine.addY x A.1 y (W.toAffine.slope x A.1 y A.2)
        + W.toAffine.addY x A.1 y (W.toAffine.slope x A.1 y (W.toAffine.negY A.1 A.2))
        - A.2 - W.toAffine.negY A.1 A.2) := by
  rw [veluY_eq_add_sum_singleton]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have key := W.veluY_singleton_eq_orbitSum (x₀ := A.1) (y₀ := A.2) hP (hSeq A hA) (hx A hA)
  rw [show ({(A.1, A.2)} : Finset (F × F)) = {A} from by simp] at key
  linear_combination key

end GeneralOrbitSum
end WeierstrassCurve
end

noncomputable section

namespace WeierstrassCurve
section GeneralOrbitSum

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
theorem veluX_eq_add_sum_singleton (S : Finset (F × F)) (x : F) :
    W.veluX S x = x + ∑ P ∈ S, (W.veluX {P} x - x) := by
  simp only [veluX, Finset.sum_singleton, add_sub_cancel_left]

theorem veluX_eq_orbitSum {S : Finset (F × F)} {x y : F} (hP : W.toAffine.Equation x y)
    (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2) (hx : ∀ A ∈ S, x ≠ A.1) :
    W.veluX S x = x + ∑ A ∈ S,
      (W.toAffine.addX x A.1 (W.toAffine.slope x A.1 y A.2)
        + W.toAffine.addX x A.1 (W.toAffine.slope x A.1 y (W.toAffine.negY A.1 A.2))
        - 2 * A.1) := by
  rw [veluX_eq_add_sum_singleton]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have key := W.veluX_singleton_eq_orbitSum (x₀ := A.1) (y₀ := A.2) hP (hSeq A hA) (hx A hA)
  rw [show ({(A.1, A.2)} : Finset (F × F)) = {A} from by simp] at key
  linear_combination key

end GeneralOrbitSum
section FullPeriod

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {p : ℕ}

theorem not_mem_zmultiples_add {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) {K : W.toAffine.Point}
    (hK : K ∈ AddSubgroup.zmultiples Q) : P + K ∉ AddSubgroup.zmultiples Q := fun hmem =>
  hPmem (by simpa using AddSubgroup.sub_mem _ hmem hK)

theorem add_ne_zero_of_not_mem_zmultiples {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) {K : W.toAffine.Point}
    (hK : K ∈ AddSubgroup.zmultiples Q) : P + K ≠ 0 := fun h =>
  hPmem (by rw [add_eq_zero_iff_eq_neg] at h; exact h ▸ AddSubgroup.neg_mem _ hK)

theorem xOrZero_ne_of_not_mem_zmultiples {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) (hP0 : P ≠ 0) {x y : F}
    {h : W.toAffine.Nonsingular x y} (hkQ : Point.some x y h ∈ AddSubgroup.zmultiples Q) :
    P.xOrZero ≠ x := by
  obtain ⟨a, b, hns, rfl, -⟩ := exists_some_of_ne_zero hP0
  intro hx
  rcases (Point.X_eq_iff (h₁ := hns) (h₂ := h)).mp hx with hPP | hPP
  · exact hPmem (hPP ▸ hkQ)
  · exact hPmem (hPP ▸ AddSubgroup.neg_mem _ hkQ)

theorem sum_range_addOrderOf_shift_invariant {G : Type*} [AddCommGroup G] {Q : G}
    {p : ℕ} (hord : addOrderOf Q = p) {M : Type*} [AddCommMonoid M] (f : G → M) (R : G) :
    ∑ j ∈ Finset.range p, f (R + Q + j • Q) = ∑ j ∈ Finset.range p, f (R + j • Q) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp
  have hpQ : p • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
  have hLHS : ∑ j ∈ Finset.range p, f (R + Q + j • Q)
      = ∑ k ∈ Finset.Ico 1 (p + 1), f (R + k • Q) := by
    rw [show Finset.Ico 1 (p + 1) = (Finset.range p).map ⟨(· + 1), add_left_injective 1⟩ from by
      ext k; simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk]
      constructor
      · exact fun ⟨h1, h2⟩ => ⟨k - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega]
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun j _ => by
      simp only [Function.Embedding.coeFn_mk]; rw [succ_nsmul', ← add_assoc]
  have hRHS : ∑ j ∈ Finset.range p, f (R + j • Q)
      = f (R + 0 • Q) + ∑ k ∈ Finset.Ico 1 p, f (R + k • Q) := by
    rw [show Finset.range p = insert 0 (Finset.Ico 1 p) from by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega]
    rw [Finset.sum_insert (by simp)]
  rw [hLHS, hRHS]
  have hIco_split : Finset.Ico 1 (p + 1) = insert p (Finset.Ico 1 p) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hIco_split, Finset.sum_insert (by simp), hpQ, zero_nsmul]

end FullPeriod
end WeierstrassCurve
end

section

section

noncomputable section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F]

section GenericPoint

variable {W : Affine F}

public theorem polyToFunctionField_X_ne_algebraMap (c : F) :
    polyToFunctionField W X ≠ algebraMap F W.FunctionField c := by
  intro hcon
  refine polyToFunctionField_ne_zero (W := W) (X_sub_C_ne_zero c) ?_
  rw [map_sub, polyToFunctionField_C, hcon, sub_self]

end GenericPoint
end Affine
end WeierstrassCurve
end

noncomputable section

namespace WeierstrassCurve
section BaseChange

variable {F F' : Type*} [Field F] [Field F'] (W : WeierstrassCurve F) (f : F →+* F')

lemma map_veluX' (S : Finset (F × F)) (hf : Function.Injective f) (x : F) :
    (W.map f).veluX (S.map ⟨Prod.map f f, hf.prodMap hf⟩) (f x) = f (W.veluX S x) := by
  simp only [veluX, Finset.sum_map, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
    map_veluT, map_veluU, map_add, map_sum, map_div₀, map_sub, map_pow]

lemma map_veluY' (S : Finset (F × F)) (hf : Function.Injective f) (x y : F) :
    (W.map f).veluY (S.map ⟨Prod.map f f, hf.prodMap hf⟩) (f x) (f y) = f (W.veluY S x y) := by
  simp only [veluY, Finset.sum_map, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
    map_veluT, map_veluU, map_veluGx, map_veluGy, map_a₁, map_a₃,
    map_add, map_sub, map_mul, map_div₀, map_pow, map_sum, map_ofNat]

theorem map_veluDeficit (S : Finset (F × F)) (hf : Function.Injective f) (r s : F) :
    (W.map f).veluDeficit (S.map ⟨Prod.map f f, hf.prodMap hf⟩) (f r) (f s)
      = f (W.veluDeficit S r s) := by
  simp only [veluDeficit, W.map_veluX' f S hf, W.map_veluY' f S hf,
    W.map_veluQuotient f S hf, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    map_add, map_sub, map_mul, map_pow]

end BaseChange
end WeierstrassCurve
namespace WeierstrassCurve
section FunctionFieldLift

variable {F : Type*} [Field F] (W : Affine F)

/-- Map the kernel-coordinate summing set into the curve's function field by extending constants. -/
@[expose] public def liftSummingSet
    (S : Finset (F × F)) : Finset (W.FunctionField × W.FunctionField) :=
  S.map ⟨Prod.map (algebraMap F W.FunctionField) (algebraMap F W.FunctionField),
    (algebraMap F W.FunctionField).injective.prodMap (algebraMap F W.FunctionField).injective⟩

/-- The candidate Vélu equation residual evaluated at the generic point as a function-field
element. -/
@[expose] public def veluDeficitFun (S : Finset (F × F)) : W.FunctionField :=
  (W.map (algebraMap F W.FunctionField)).veluDeficit (W.liftSummingSet S)
    (polyToFunctionField W X) (yGen W)

end FunctionFieldLift
end WeierstrassCurve
end
section

open scoped Pointwise

noncomputable section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

section MemEval

theorem XClass_mem_XYIdeal_iff_eq {x' y' : F} (h' : W.Equation x' y') (a : F) :
    XClass W a ∈ XYIdeal W x' (C y') ↔ x' = a := by
  rw [show (XClass W a : W.CoordinateRing) = CoordinateRing.mk W (C (X - C a)) from rfl,
    mk_mem_XYIdeal_iff h']
  simp [evalEval, sub_eq_zero]

theorem YClass_C_mem_XYIdeal_iff_eq {x' y' : F} (h' : W.Equation x' y') (c : F) :
    YClass W (C c) ∈ XYIdeal W x' (C y') ↔ y' = c := by
  rw [show (YClass W (C c) : W.CoordinateRing) = CoordinateRing.mk W (Y - C (C c)) from rfl,
    mk_mem_XYIdeal_iff h']
  simp [evalEval, sub_eq_zero]

end MemEval
section PerCurveEngine

variable [IsAlgClosed F] [IsDedekindDomain W.CoordinateRing]

theorem exists_YClass_negY_notMem_centre {v : Place F W.FunctionField} (hv : IsFinitePlace v)
    {a b₀ : F} (hab₀ : W.Equation a b₀) (h2tor : W.negY a b₀ ≠ b₀)
    (hXa : XClass W a ∈ hv.centre) :
    ∃ b : F, W.Equation a b ∧ XClass W a ∈ hv.centre ∧
      YClass W (C (W.negY a b)) ∉ hv.centre := by
  classical
  obtain ⟨x', y', h', rfl⟩ := (isFinitePlace_iff_exists_placeOfEquation v).mp hv
  have hcen : hv.centre = XYIdeal W x' (C y') := by
    rw [Subsingleton.elim hv (isFinitePlace_placeOfEquation h')]; exact centre_placeOfEquation h'
  have hxa : x' = a := (XClass_mem_XYIdeal_iff_eq h' a).mp (hcen ▸ hXa)
  subst hxa
  refine ⟨y', h', hXa, hcen ▸ ?_⟩
  refine fun hmem => ?_
  have heq : y' = W.negY x' y' := (YClass_C_mem_XYIdeal_iff_eq h' (W.negY x' y')).mp hmem
  rcases Y_eq_of_X_eq h' hab₀ rfl with hy | hy
  · exact h2tor (hy ▸ heq.symm)
  · rw [hy, negY_negY] at heq; exact h2tor heq

end PerCurveEngine
end Affine
end WeierstrassCurve
namespace WeierstrassCurve
section YNotCentreDischarge

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F]

open AlgebraicCurve WeierstrassCurve.Affine.CoordinateRing WeierstrassCurve.Affine

theorem negY_ne_self_of_veluGy_ne_zero {R : Type*} [CommRing R] {W : WeierstrassCurve R}
    {a b : R} (hgy : W.veluGy a b ≠ 0) : W.toAffine.negY a b ≠ b := by
  intro heq
  apply hgy
  have hkey : W.toAffine.negY a b - b = W.veluGy a b := by
    simp only [Affine.negY, veluGy]; ring
  rw [← hkey, heq, sub_self]

end YNotCentreDischarge
end WeierstrassCurve

end

end

section

noncomputable section

namespace WeierstrassCurve
section ReducedCofactor

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluDeficitPsiCofactorReduced (x₀ x : R) : R :=
  -6 * x ^ 3 + 18 * x₀ * x ^ 2 + (2 * W.b₂ * x₀ + 2 * W.b₄ - 6 * x₀ ^ 2) * x
    + (6 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 4 * W.b₄ * x₀ + 3 * W.b₆)

theorem veluDeficitPsiCofactor_eq_sq_mul_reduced (x₀ x : R) :
    W.veluDeficitPsiCofactor x₀ x = (x - x₀) ^ 2 * W.veluDeficitPsiCofactorReduced x₀ x := by
  simp only [veluDeficitPsiCofactor, veluDeficitPsiCofactorReduced, b₂, b₄, b₆]
  ring

def veluDeficitPsiCofactorReducedPoly (x₀ : R) : R[X] :=
  C (-6) * X ^ 3 + C (18 * x₀) * X ^ 2 + C (2 * W.b₂ * x₀ + 2 * W.b₄ - 6 * x₀ ^ 2) * X
    + C (6 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 4 * W.b₄ * x₀ + 3 * W.b₆)

@[scoped simp] lemma eval_veluDeficitPsiCofactorReducedPoly (x₀ x : R) :
    (W.veluDeficitPsiCofactorReducedPoly x₀).eval x = W.veluDeficitPsiCofactorReduced x₀ x := by
  simp [veluDeficitPsiCofactorReducedPoly, veluDeficitPsiCofactorReduced]

lemma veluDeficitPsiCofactorReducedPoly_natDegree_le (x₀ : R) :
    (W.veluDeficitPsiCofactorReducedPoly x₀).natDegree ≤ 3 := by
  unfold veluDeficitPsiCofactorReducedPoly
  compute_degree

end ReducedCofactor
section ReducedField

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_singleton_mul_pow_four_eq {x₀ y₀ r s : F}
    (hP : W.toAffine.Equation r s) (hQ : W.toAffine.Equation x₀ y₀) (hr : r ≠ x₀) :
    W.veluDeficit {(x₀, y₀)} r s * (r - x₀) ^ 4
      = W.veluDeficitPsiCofactorReduced x₀ r * (W.Ψ₃).eval x₀ := by
  have hd : (r - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hr)
  have key := W.veluDeficit_singleton_mul_pow_eq_psi hP hQ hr
  rw [W.veluDeficitPsiCofactor_eq_sq_mul_reduced] at key
  have h64 : (r - x₀) ^ 6 = (r - x₀) ^ 4 * (r - x₀) ^ 2 := by ring
  rw [h64, ← mul_assoc] at key
  exact mul_right_cancel₀ hd (by linear_combination key)

end ReducedField
section RRCarrier

variable (F : Type*) [Field F] [DecidableEq F]

/-- For a cyclic kernel of order `p`, the equation residual is constant on curve points away from
the kernel's `x`-coordinates. -/
@[expose] public def VeluDeficitIsConstantAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ c : F, ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = c

end RRCarrier
section ConstantZero

variable {F : Type*} [Field F]

variable (F)
variable [DecidableEq F]

/-- Any constant equal to the cyclic-kernel equation residual at every allowed curve point must
be zero. -/
@[expose] public def VeluDeficitConstantIsZeroAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ c : F, (∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = c) →
          c = 0

public theorem veluDeficitConstancyAt_of_isConstant_of_constantZero {p : ℕ}
    (hC : VeluDeficitIsConstantAt F p) (hZ : VeluDeficitConstantIsZeroAt F p) :
    VeluDeficitConstancyAt F p := by
  intro W hΔ x₀ y₀ h₀ hord r s hrs hav
  obtain ⟨c, hc⟩ := hC W hΔ x₀ y₀ h₀ hord
  rw [hc hrs hav, hZ W hΔ x₀ y₀ h₀ hord c hc]

end ConstantZero
end WeierstrassCurve
end
noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable [HasPrincipalDivisors K F]

theorem eq_algebraMap_of_forall_ord_nonneg (v₀ : Place K F) (hrat : v₀.IsRational)
    (hdeg : v₀.deg ≠ 0) {g : F} (hg : g ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  have hg₀ : g ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hg (hord v₀)
  refine ⟨v₀.evalAt g, ?_⟩
  by_contra hne
  set t : F := g - algebraMap K F (v₀.evalAt g) with ht
  have htne : t ≠ 0 := sub_ne_zero.mpr hne
  have hzero : 0 < v₀.ord t := v₀.ord_sub_evalAt_pos hrat hg₀ htne
  have hpole : ∀ v : Place K F, 0 ≤ v.ord t := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hg (hord v)) (v.algebraMap_mem' _))
  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) t htne
  have hDpos : 0 < D v₀ := by rw [hD v₀]; exact hzero
  have hDnonneg : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hpole v
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hDpos.ne'
  have hpos : 0 < Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) :=
          mul_pos hDpos (by exact_mod_cast Nat.pos_of_ne_zero hdeg)
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hDnonneg v) (Int.natCast_nonneg _)) hmem
  omega

end Place
end AlgebraicCurve
end
section

noncomputable section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F]

section TranslationCoords

variable (W : Affine F) (a b : F)

local notation "ι" => algebraMap F W.FunctionField

def addXFun : W.FunctionField :=
  (W.map ι).addX (polyToFunctionField W X) (ι a)
    ((W.map ι).slope (polyToFunctionField W X) (ι a) (yGen W) (ι b))

def addYFun : W.FunctionField :=
  (W.map ι).addY (polyToFunctionField W X) (ι a) (yGen W)
    ((W.map ι).slope (polyToFunctionField W X) (ι a) (yGen W) (ι b))

variable {a b} in
theorem equation_map_addFun (hA : W.Equation a b) :
    (W.map ι).Equation (W.addXFun a b) (W.addYFun a b) :=
  Affine.equation_add (W := (W.map ι).toAffine)
    equation_map_polyToFunctionField_yGen (hA.map ι)
    (fun h => polyToFunctionField_X_ne_algebraMap a h.1)

variable {a b} in
theorem eval₂_polynomial_addFun (hA : W.Equation a b) :
    W.polynomial.eval₂
      (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom (W.addYFun a b) = 0 := by
  have heq := equation_map_addFun W hA
  rw [equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination heq

end TranslationCoords
section GenericPointGroup

variable {W : Affine F}

local notation "ι" => algebraMap F W.FunctionField

theorem map_functionField_Δ_ne_zero (hΔ : W.Δ ≠ 0) : (W.map ι).Δ ≠ 0 := by
  rw [map_Δ]
  exact fun h => hΔ ((algebraMap F W.FunctionField).injective (by simpa using h))

theorem nonsingular_map_polyToFunctionField_yGen (hΔ : W.Δ ≠ 0) :
    (W.map ι).Nonsingular (polyToFunctionField W X) (yGen W) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (map_functionField_Δ_ne_zero hΔ)).mp
    equation_map_polyToFunctionField_yGen

def genericPoint' (hΔ : W.Δ ≠ 0) : (W.map ι).toAffine.Point :=
  Affine.Point.some (polyToFunctionField W X) (yGen W)
    (nonsingular_map_polyToFunctionField_yGen hΔ)

theorem nonsingular_map_algebraMap (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).Nonsingular (ι a) (ι b) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (map_functionField_Δ_ne_zero hΔ)).mp (hA.map ι)

def mapPoint (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) : (W.map ι).toAffine.Point :=
  Affine.Point.some (ι a) (ι b) (nonsingular_map_algebraMap hΔ hA)

theorem nonsingular_map_addFun (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).Nonsingular (W.addXFun a b) (W.addYFun a b) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (map_functionField_Δ_ne_zero hΔ)).mp
    (equation_map_addFun W hA)

theorem genericPoint'_add_map (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    genericPoint' hΔ + mapPoint hΔ hA
      = Affine.Point.some (W.addXFun a b) (W.addYFun a b) (nonsingular_map_addFun hΔ hA) :=
  Affine.Point.add_of_X_ne (polyToFunctionField_X_ne_algebraMap a)

theorem equation_neg_mapPoint {a b : F} (hA : W.Equation a b) : W.Equation a (W.negY a b) :=
  (Affine.equation_neg a b).mpr hA

theorem addFun_ne_mapPoint (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    ¬ (W.addXFun a b = ι a ∧ W.addYFun a b = ι b) := by
  intro ⟨hX, hY⟩
  have heq : Affine.Point.some _ _ (nonsingular_map_addFun hΔ hA) = mapPoint hΔ hA := by
    change Affine.Point.some _ _ _ = Affine.Point.some _ _ _
    simp only [Affine.Point.some.injEq]; exact ⟨hX, hY⟩
  have h0 : genericPoint' hΔ + mapPoint hΔ hA = 0 + mapPoint hΔ hA := by
    rw [zero_add]; exact (genericPoint'_add_map hΔ hA).trans heq
  exact Affine.Point.some_ne_zero _ (add_right_cancel h0)

theorem neg_mapPoint_eq (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    -(mapPoint hΔ hA) = Affine.Point.some (ι a) (ι (W.negY a b))
      (nonsingular_map_algebraMap hΔ (equation_neg_mapPoint hA)) := by
  change Affine.Point.some (ι a) ((W.map ι).negY (ι a) (ι b)) _ = _
  congr 1
  exact map_negY ι a b

theorem addFun_neg_mapPoint_hxy (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    ¬ (W.addXFun a b = ι a
        ∧ W.addYFun a b = (W.map ι).negY (ι a) (ι (W.negY a b))) := by
  rw [map_negY ι a (W.negY a b), Affine.negY_negY]
  exact addFun_ne_mapPoint hΔ hA

theorem addFun_neg_cancel (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).addX (W.addXFun a b) (ι a)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = polyToFunctionField W X
    ∧ (W.map ι).addY (W.addXFun a b) (ι a) (W.addYFun a b)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = yGen W := by
  have hns₂ := Affine.nonsingular_add (nonsingular_map_addFun hΔ hA)
      (nonsingular_map_algebraMap hΔ (equation_neg_mapPoint hA))
      (addFun_neg_mapPoint_hxy hΔ hA)
  have hsum : (Affine.Point.some _ _ (nonsingular_map_addFun hΔ hA))
        + (-(mapPoint hΔ hA))
      = Affine.Point.some _ _ hns₂ := by
    rw [neg_mapPoint_eq hΔ hA]
    exact Affine.Point.add_some (addFun_neg_mapPoint_hxy hΔ hA)
  have hcancel : Affine.Point.some _ _ hns₂ = genericPoint' hΔ := by
    rw [← hsum, ← genericPoint'_add_map hΔ hA, add_neg_cancel_right]
  exact Affine.Point.some.inj hcancel

theorem addFun_neg_cancel_X (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).addX (W.addXFun a b) (ι a)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = polyToFunctionField W X :=
  (addFun_neg_cancel hΔ hA).1

theorem addFun_neg_cancel_Y (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b) :
    (W.map ι).addY (W.addXFun a b) (ι a) (W.addYFun a b)
        ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b)))
      = yGen W :=
  (addFun_neg_cancel hΔ hA).2

end GenericPointGroup
section CoordHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

def translationCoordHom : W.CoordinateRing →ₐ[F] W.FunctionField where
  __ := AdjoinRoot.lift
    (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom
    (W.addYFun a b) (eval₂_polynomial_addFun W hA)
  commutes' c := by
    change AdjoinRoot.lift _ _ (eval₂_polynomial_addFun W hA) (algebraMap F _ c)
      = algebraMap F W.FunctionField c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

theorem translationCoordHom_mk (g : F[X][Y]) :
    translationCoordHom hA (CoordinateRing.mk W g)
      = g.eval₂ (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom (W.addYFun a b) :=
  AdjoinRoot.lift_mk (eval₂_polynomial_addFun W hA) g

theorem translationCoordHom_comp_algebraMap :
    (translationCoordHom hA).toRingHom.comp (algebraMap F[X] W.CoordinateRing)
      = (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom := by
  refine RingHom.ext fun p => ?_
  change translationCoordHom hA (algebraMap F[X] _ p) = _
  rw [algebraMap_polynomial_eq_mk_C, translationCoordHom_mk, eval₂_C]

@[scoped simp] theorem translationCoordHom_XClass :
    translationCoordHom hA (algebraMap F[X] W.CoordinateRing X) = W.addXFun a b := by
  rw [algebraMap_polynomial_eq_mk_C, translationCoordHom_mk, eval₂_C]
  exact Polynomial.aeval_X _

@[scoped simp] theorem translationCoordHom_YClass :
    translationCoordHom hA (CoordinateRing.mk W Y) = W.addYFun a b := by
  rw [translationCoordHom_mk]
  exact eval₂_X _ _

end CoordHom
section AdjoinSurjective

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

theorem slope_mem_intermediateField {K : IntermediateField F W.FunctionField}
    {x₁ x₂ y₁ y₂ : W.FunctionField}
    (hx₁ : x₁ ∈ K) (hx₂ : x₂ ∈ K) (hy₁ : y₁ ∈ K) (hy₂ : y₂ ∈ K) :
    (W.map ι).slope x₁ x₂ y₁ y₂ ∈ K := by
  have hF : ∀ c : F, ι c ∈ K := fun c => (algebraMap F K c).2
  have hN : ∀ n : ℕ, (n : W.FunctionField) ∈ K := fun n => natCast_mem K n
  unfold Affine.slope
  split
  · split
    · exact zero_mem K
    · simp only [map_a₁, map_a₂, map_a₄]
      refine div_mem (sub_mem (add_mem (add_mem (mul_mem (hN 3) (pow_mem hx₁ 2))
        (mul_mem (mul_mem (hN 2) (hF _)) hx₁)) (hF _)) (mul_mem (hF _) hy₁)) (sub_mem hy₁ ?_)
      unfold Affine.negY
      simp only [map_a₁, map_a₃]
      exact sub_mem (sub_mem (neg_mem hy₁) (mul_mem (hF _) hx₁)) (hF _)
  · exact div_mem (sub_mem hy₁ hy₂) (sub_mem hx₁ hx₂)

include hΔ hA in
theorem polyToFunctionField_X_mem_adjoin_addFun :
    polyToFunctionField W X
      ∈ IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) := by
  set K := IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
  rw [← addFun_neg_cancel_X hΔ hA]
  have hX' : W.addXFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inl rfl)
  have hY' : W.addYFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inr rfl)
  have hF : ∀ c : F, ι c ∈ K := fun c => (algebraMap F K c).2
  have hslope := slope_mem_intermediateField (W := W) hX' (hF a) hY' (hF (W.negY a b))
  change (W.map ι).addX (W.addXFun a b) (ι a) _ ∈ K
  rw [Affine.addX]
  simp only [map_a₁, map_a₂]
  exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hslope 2) (mul_mem (hF _) hslope))
    (hF _)) hX') (hF _)

include hΔ hA in
theorem yGen_mem_adjoin_addFun :
    yGen W
      ∈ IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) := by
  set K := IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
  rw [← addFun_neg_cancel_Y hΔ hA]
  have hX' : W.addXFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inl rfl)
  have hY' : W.addYFun a b ∈ K := IntermediateField.subset_adjoin F _ (Or.inr rfl)
  have hF : ∀ c : F, ι c ∈ K := fun c => (algebraMap F K c).2
  have hslope := slope_mem_intermediateField (W := W) hX' (hF a) hY' (hF (W.negY a b))
  have haddX : (W.map ι).addX (W.addXFun a b) (ι a)
      ((W.map ι).slope (W.addXFun a b) (ι a) (W.addYFun a b) (ι (W.negY a b))) ∈ K := by
    rw [Affine.addX]
    simp only [map_a₁, map_a₂]
    exact sub_mem (sub_mem (sub_mem (add_mem (pow_mem hslope 2) (mul_mem (hF _) hslope))
      (hF _)) hX') (hF _)
  change (W.map ι).addY (W.addXFun a b) (ι a) (W.addYFun a b) _ ∈ K
  rw [Affine.addY, Affine.negY, Affine.negAddY]
  simp only [map_a₁, map_a₃]
  exact sub_mem (sub_mem (neg_mem (add_mem (mul_mem hslope (sub_mem haddX hX')) hY'))
    (mul_mem (hF _) haddX)) (hF _)

include hΔ hA in
theorem adjoin_addFun_eq_top :
    IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  set K := IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
  have hX : polyToFunctionField W X ∈ K := polyToFunctionField_X_mem_adjoin_addFun hΔ hA
  have hY : yGen W ∈ K := yGen_mem_adjoin_addFun hΔ hA
  have hpoly : ∀ p : F[X], polyToFunctionField W p ∈ K := by
    intro p
    induction p using Polynomial.induction_on' with
    | add g h hg hh => rw [map_add]; exact add_mem hg hh
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C]
        exact mul_mem (algebraMap F K c).2 (pow_mem hX n)
  have hcr : ∀ r : W.CoordinateRing,
      algebraMap W.CoordinateRing W.FunctionField r ∈ K := by
    intro r
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq (W' := W) r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly p) (mul_mem (hpoly q) hY)
  rw [← hrs]
  exact div_mem (hcr r) (hcr s)

end AdjoinSurjective
section TranslationHom

variable {W : Affine F} {a b : F} (hA : W.Equation a b)

def AddXFunTranscendental (W : Affine F) (a b : F) : Prop :=
  Transcendental F (W.addXFun a b)

variable (htr : AddXFunTranscendental W a b)

include htr in
theorem translationCoordHom_injective : Function.Injective (translationCoordHom hA) := by
  have hker : RingHom.ker (translationCoordHom hA).toRingHom = ⊥ := by
    have : Module.Finite F[X] W.CoordinateRing :=
      Module.Finite.of_basis (CoordinateRing.basis W)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, translationCoordHom_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact (injective_iff_map_eq_zero _).mpr fun p hp => transcendental_iff.mp htr p hp
  exact (RingHom.injective_iff_ker_eq_bot (translationCoordHom hA).toRingHom).mpr hker

def translationHom : W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (translationCoordHom_injective hA htr)

theorem translationHom_algebraMap (r : W.CoordinateRing) :
    translationHom hA htr (algebraMap W.CoordinateRing W.FunctionField r)
      = translationCoordHom hA r :=
  IsFractionRing.lift_algebraMap (translationCoordHom_injective hA htr) r

@[scoped simp] theorem translationHom_polyToFunctionField_X :
    translationHom hA htr (polyToFunctionField W X) = W.addXFun a b := by
  rw [polyToFunctionField_apply, translationHom_algebraMap, ← translationCoordHom_XClass hA]

@[scoped simp] theorem translationHom_yGen :
    translationHom hA htr (yGen W) = W.addYFun a b := by
  change translationHom hA htr (algebraMap _ _ (CoordinateRing.mk W Y)) = _
  rw [translationHom_algebraMap, translationCoordHom_YClass]

variable (hΔ : W.Δ ≠ 0)

include hΔ in
theorem translationHom_surjective : Function.Surjective (translationHom hA htr) := by
  intro z
  have hz : z ∈ IntermediateField.adjoin F
      ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) := by
    rw [adjoin_addFun_eq_top hΔ hA]; trivial
  have hle : IntermediateField.adjoin F
      ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)
      ≤ (translationHom hA htr).fieldRange := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ (rfl | rfl)
    · exact ⟨polyToFunctionField W X, translationHom_polyToFunctionField_X hA htr⟩
    · exact ⟨yGen W, translationHom_yGen hA htr⟩
  exact hle hz

def translationAlgEquiv : W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofBijective (translationHom hA htr)
    ⟨(translationHom hA htr).injective, translationHom_surjective hA htr hΔ⟩

end TranslationHom
end Affine
end WeierstrassCurve
end

noncomputable section

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

section OrdPins

variable (v : Place F W.FunctionField)

theorem ord_X_sub_algebraMap_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c : F) :
    v.ord (polyToFunctionField W X - algebraMap F W.FunctionField c) = -2 := by
  have key : polyToFunctionField W X - algebraMap F W.FunctionField c
      = polyToFunctionField W (X - C c) := by
    rw [map_sub, polyToFunctionField_C]
  rw [key, v.ord_ringHom_eq_natDegree_mul polyToFunctionField_injective polyToFunctionField_C
    (ord_X_neg_of_not_isFinitePlace v hv) (X_sub_C_ne_zero c), natDegree_X_sub_C,
    ord_X_eq_neg_two_of_not_isFinitePlace v hv]
  norm_num

theorem X_sub_algebraMap_ne_zero (c : F) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c : W.FunctionField) ≠ 0 :=
  sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap c)

theorem inv_X_sub_algebraMap_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c : F) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹ ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg (inv_ne_zero (X_sub_algebraMap_ne_zero c)) ?_
  rw [v.ord_inv, ord_X_sub_algebraMap_of_not_isFinitePlace v hv]
  omega

theorem X_mul_inv_X_sub_algebraMap_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c : F) :
    polyToFunctionField W X * (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹
      ∈ v.toValuationSubring := by
  refine v.mem_of_ord_nonneg
    (mul_ne_zero (polyToFunctionField_ne_zero X_ne_zero)
      (inv_ne_zero (X_sub_algebraMap_ne_zero c))) ?_
  rw [v.ord_mul (polyToFunctionField_ne_zero X_ne_zero)
    (inv_ne_zero (X_sub_algebraMap_ne_zero c)), v.ord_inv,
    ord_X_eq_neg_two_of_not_isFinitePlace v hv,
    ord_X_sub_algebraMap_of_not_isFinitePlace v hv]
  omega

theorem ord_yGen_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) :
    v.ord (yGen W) = -3 :=
  ord_Y_eq_neg_three_of_not_isFinitePlace v hv

theorem yGen_mul_inv_X_sub_algebraMap_sq_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (c : F) :
    yGen W * ((polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹) ^ 2
      ∈ v.toValuationSubring := by
  have hY : yGen W ≠ (0 : W.FunctionField) := Y_image_ne_zero
  have hinv : (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹
      ≠ (0 : W.FunctionField) := inv_ne_zero (X_sub_algebraMap_ne_zero c)
  refine v.mem_of_ord_nonneg (mul_ne_zero hY (pow_ne_zero 2 hinv)) ?_
  rw [v.ord_mul hY (pow_ne_zero 2 hinv), v.ord_pow, v.ord_inv,
    ord_X_sub_algebraMap_of_not_isFinitePlace v hv, ord_yGen_of_not_isFinitePlace v hv]
  omega

theorem natCast_mem (n : ℕ) : (n : W.FunctionField) ∈ v.toValuationSubring := by
  rw [show (n : W.FunctionField) = algebraMap F W.FunctionField n from (map_natCast _ n).symm]
  exact v.algebraMap_mem' (n : F)

theorem veluTSum_liftSummingSet_mem (S : Finset (F × F)) :
    (W.map (algebraMap F W.FunctionField)).veluTSum (W.liftSummingSet S)
      ∈ v.toValuationSubring := by
  unfold WeierstrassCurve.veluTSum
  refine sum_mem fun Q hQ => ?_
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  rw [Prod.map_fst, Prod.map_snd, map_veluT]
  exact v.algebraMap_mem' _

end OrdPins

section LaurentLift

variable (W)

local notation "W'" => W.map (algebraMap F W.FunctionField)

theorem equation_of_mem_liftSummingSet {S : Finset (F × F)}
    (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    ∀ A ∈ W.liftSummingSet S, (W').toAffine.Equation A.1 A.2 := by
  intro A hA
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  exact (hS B hB).map (algebraMap F W.FunctionField)

public theorem polyToFunctionField_X_ne_of_mem_liftSummingSet {S : Finset (F × F)} :
    ∀ A ∈ W.liftSummingSet S, polyToFunctionField W X ≠ A.1 := by
  intro A hA
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hA
  obtain ⟨B, -, rfl⟩ := hA
  exact polyToFunctionField_X_ne_algebraMap B.1

theorem veluDeficitFun_eq_laurentSum_add_bracket {S : Finset (F × F)}
    (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    W.veluDeficitFun S
      = (∑ Q ∈ W.liftSummingSet S, (-((W').veluU Q.1 Q.2) ^ 2 / (polyToFunctionField W X - Q.1) ^ 3
          - 3 * (W').veluT Q.1 Q.2 * (W').veluU Q.1 Q.2 / (polyToFunctionField W X - Q.1) ^ 2
          - (3 * ((W').veluT Q.1 Q.2) ^ 2 + 6 * ((W').Ψ₃).eval Q.1)
              / (polyToFunctionField W X - Q.1)))
        + (W').veluDeficitBracket (W.liftSummingSet S) (polyToFunctionField W X) (yGen W) :=
  (W').veluDeficit_eq_laurentSum_add_bracket equation_map_polyToFunctionField_yGen
    (equation_of_mem_liftSummingSet W hS) (polyToFunctionField_X_ne_of_mem_liftSummingSet W)

end LaurentLift

section Corrections

variable {v : Place F W.FunctionField}

local notation "W'" => W.map (algebraMap F W.FunctionField)
local notation "ι" => algebraMap F W.FunctionField
local notation "𝕏" => polyToFunctionField W X
local notation "𝕐" => yGen W

theorem veluXCorr_genericPoint'_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c d : F) :
    (W').veluXCorr (ι c) (ι d) 𝕏 ∈ v.toValuationSubring := by
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv c
  unfold WeierstrassCurve.veluXCorr
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, map_veluT, map_veluU]
  exact add_mem (mul_mem (v.algebraMap_mem' _) hδ)
    (mul_mem (v.algebraMap_mem' _) (pow_mem hδ 2))

theorem veluYCorr_genericPoint'_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v) (c d : F) :
    (W').veluYCorr (ι c) (ι d) 𝕏 𝕐 ∈ v.toValuationSubring := by
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv c
  have hXδ := X_mul_inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv c
  have hYδ := yGen_mul_inv_X_sub_algebraMap_sq_mem_of_not_isFinitePlace v hv c
  set δ : W.FunctionField := (𝕏 - ι c)⁻¹ with hδdef
  have key : (W').veluYCorr (ι c) (ι d) 𝕏 𝕐
      = -((2 * ι (W.veluU c d)) * (𝕐 * δ ^ 2) * δ
          + (ι (W.a₁ * W.veluU c d)) * (𝕏 * δ) * δ ^ 2
          + (ι (W.a₃ * W.veluU c d)) * δ ^ 3
          + (ι (W.a₁ * W.veluT c d)) * δ
          + (ι (W.veluT c d)) * (𝕐 * δ ^ 2)
          + (-ι (d * W.veluT c d)) * δ ^ 2
          + (ι (W.a₁ * W.veluU c d - W.veluGx c d * W.veluGy c d)) * δ ^ 2) := by
    have hδne : (𝕏 - ι c : W.FunctionField) ≠ 0 := X_sub_algebraMap_ne_zero c
    unfold WeierstrassCurve.veluYCorr
    simp only [map_veluU, map_veluT, map_veluGx, map_veluGy, map_a₁, map_a₃, map_mul, map_sub]
    rw [hδdef]
    field_simp
    ring
  rw [key]
  have h2 : (2 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 2; push_cast at this; exact this
  refine neg_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_) ?_)
  · exact mul_mem (mul_mem (mul_mem h2 (v.algebraMap_mem' _)) hYδ) hδ
  · exact mul_mem (mul_mem (v.algebraMap_mem' _) hXδ) (pow_mem hδ 2)
  · exact mul_mem (v.algebraMap_mem' _) (pow_mem hδ 3)
  · exact mul_mem (v.algebraMap_mem' _) hδ
  · exact mul_mem (v.algebraMap_mem' _) hYδ
  · exact mul_mem (neg_mem (v.algebraMap_mem' _)) (pow_mem hδ 2)
  · exact mul_mem (v.algebraMap_mem' _) (pow_mem hδ 2)

public theorem veluX_sub_self_genericPoint'_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    (W').veluX (W.liftSummingSet S) 𝕏 - 𝕏 ∈ v.toValuationSubring := by
  rw [(W').veluX_sub_self_eq_sum_veluXCorr]
  refine sum_mem fun Q hQ => ?_
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  exact veluXCorr_genericPoint'_mem_of_not_isFinitePlace hv B.1 B.2

theorem veluY_sub_self_genericPoint'_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    (W').veluY (W.liftSummingSet S) 𝕏 𝕐 - 𝕐 ∈ v.toValuationSubring := by
  rw [(W').veluY_sub_self_eq_sum_veluYCorr]
  refine sum_mem fun Q hQ => ?_
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  exact veluYCorr_genericPoint'_mem_of_not_isFinitePlace hv B.1 B.2

theorem X_mul_veluX_sub_self_genericPoint'_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    𝕏 * ((W').veluX (W.liftSummingSet S) 𝕏 - 𝕏) ∈ v.toValuationSubring := by
  rw [mul_comm, (W').veluX_sub_self_mul_r (W.liftSummingSet S)
    (polyToFunctionField_X_ne_of_mem_liftSummingSet W)]
  refine add_mem (veluTSum_liftSummingSet_mem v S) (sum_mem fun Q hQ => ?_)
  · simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
    obtain ⟨B, -, rfl⟩ := hQ
    have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv B.1
    simp only [Prod.map_fst, Prod.map_snd, map_veluW, map_veluU, div_eq_mul_inv, ← inv_pow]
    exact add_mem (mul_mem (v.algebraMap_mem' _) hδ)
      (mul_mem (mul_mem (v.algebraMap_mem' _) (v.algebraMap_mem' _)) (pow_mem hδ 2))

end Corrections

section Engine

variable {v : Place F W.FunctionField}

local notation "W'" => W.map (algebraMap F W.FunctionField)
local notation "ι" => algebraMap F W.FunctionField
local notation "𝕏" => polyToFunctionField W X
local notation "𝕐" => yGen W

theorem veluDeficitBracket_genericPoint'_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    (S : Finset (F × F)) :
    (W').veluDeficitBracket (W.liftSummingSet S) 𝕏 𝕐 ∈ v.toValuationSubring := by
  set α := (W').veluX (W.liftSummingSet S) 𝕏 - 𝕏 with hαdef
  set β := (W').veluY (W.liftSummingSet S) 𝕏 𝕐 - 𝕐 with hβdef
  have hα : α ∈ v.toValuationSubring :=
    veluX_sub_self_genericPoint'_mem_of_not_isFinitePlace hv S
  have hβ : β ∈ v.toValuationSubring :=
    veluY_sub_self_genericPoint'_mem_of_not_isFinitePlace hv S
  have hXα : 𝕏 * α ∈ v.toValuationSubring :=
    X_mul_veluX_sub_self_genericPoint'_mem_of_not_isFinitePlace hv S
  have ht : (W').veluTSum (W.liftSummingSet S) ∈ v.toValuationSubring :=
    veluTSum_liftSummingSet_mem v S
  have h5 : (5 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 5; push_cast at this; exact this
  have h3 : (3 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 3; push_cast at this; exact this
  have key : (W').veluDeficitBracket (W.liftSummingSet S) 𝕏 𝕐
      = β ^ 2 + ι W.a₁ * α * β - (3 * (𝕏 * α) * α + ι W.a₂ * α ^ 2) - α ^ 3
        + 5 * (W').veluTSum (W.liftSummingSet S) * α := by
    unfold WeierstrassCurve.veluDeficitBracket
    rw [← hαdef, ← hβdef, map_a₁, map_a₂]
    ring
  rw [key]
  exact add_mem (sub_mem (sub_mem (add_mem (pow_mem hβ 2)
    (mul_mem (mul_mem (v.algebraMap_mem' _) hα) hβ))
    (add_mem (mul_mem (mul_mem h3 hXα) hα) (mul_mem (v.algebraMap_mem' _) (pow_mem hα 2))))
    (pow_mem hα 3)) (mul_mem (mul_mem h5 ht) hα)

theorem veluDeficitFun_mem_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    W.veluDeficitFun S ∈ v.toValuationSubring := by
  rw [veluDeficitFun_eq_laurentSum_add_bracket W hS]
  refine add_mem (sum_mem fun Q hQ => ?_)
    (veluDeficitBracket_genericPoint'_mem_of_not_isFinitePlace hv S)
  simp only [liftSummingSet, Finset.mem_map, Function.Embedding.coeFn_mk] at hQ
  obtain ⟨B, -, rfl⟩ := hQ
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv B.1
  have hδ2 : ((𝕏 - ι B.1)⁻¹ : W.FunctionField) ^ 2 ∈ v.toValuationSubring := pow_mem hδ 2
  have hδ3 : ((𝕏 - ι B.1)⁻¹ : W.FunctionField) ^ 3 ∈ v.toValuationSubring := pow_mem hδ 3
  have h3 : (3 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 3; push_cast at this; exact this
  have h6 : (6 : W.FunctionField) ∈ v.toValuationSubring := by
    have := natCast_mem v 6; push_cast at this; exact this
  rw [Prod.map_fst, Prod.map_snd, map_veluU, map_veluT,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
  refine sub_mem (sub_mem (mul_mem ?_ hδ3) (mul_mem ?_ hδ2)) (mul_mem ?_ hδ)
  · exact neg_mem (pow_mem (v.algebraMap_mem' _) 2)
  · exact mul_mem (mul_mem h3 (v.algebraMap_mem' _)) (v.algebraMap_mem' _)
  · have hΨ : ((W').Ψ₃).eval (ι B.1) = ι (W.Ψ₃.eval B.1) := by
      rw [WeierstrassCurve.map_Ψ₃, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hΨ]
    exact add_mem (mul_mem h3 (pow_mem (v.algebraMap_mem' _) 2))
      (mul_mem h6 (v.algebraMap_mem' _))

theorem ord_veluDeficitFun_nonneg_of_not_isFinitePlace (hv : ¬ IsFinitePlace v)
    {S : Finset (F × F)} (hS : ∀ A ∈ S, W.Equation A.1 A.2) :
    0 ≤ v.ord (W.veluDeficitFun S) :=
  v.ord_nonneg_of_mem (veluDeficitFun_mem_of_not_isFinitePlace hv hS)

end Engine

end Affine
end WeierstrassCurve

end

section

noncomputable section

namespace WeierstrassCurve
section ClearedPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
def veluKernelDenom (S : Finset (F × F)) : F[X] := ∏ A ∈ S, (X - C A.1)

omit [DecidableEq F] in
lemma veluKernelDenom_monic (S : Finset (F × F)) :
    (veluKernelDenom (F := F) S).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

omit [DecidableEq F] in
lemma veluKernelDenom_natDegree (S : Finset (F × F)) :
    (veluKernelDenom (F := F) S).natDegree = S.card := by
  unfold veluKernelDenom
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

omit [DecidableEq F] in
lemma eval_veluKernelDenom (S : Finset (F × F)) (r : F) :
    (veluKernelDenom (F := F) S).eval r = ∏ A ∈ S, (r - A.1) := by
  simp [veluKernelDenom, eval_prod]

def veluDeficitSingletonSumClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, C ((W.Ψ₃).eval A.1) * W.veluDeficitPsiCofactorReducedPoly A.1
    * (∏ B ∈ S.erase A, (X - C B.1)) ^ 4

theorem veluDeficit_sum_singleton_mul_prodPow_eq {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (hav : ∀ A ∈ S, r ≠ A.1) :
    (∑ A ∈ S, W.veluDeficit {A} r s) * (∏ A ∈ S, (r - A.1)) ^ 4
      = (W.veluDeficitSingletonSumClearedPoly S).eval r := by
  rw [veluDeficitSingletonSumClearedPoly, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 4
      = (r - A.1) ^ 4 * (∏ B ∈ S.erase A, (r - B.1)) ^ 4 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, ← mul_assoc,
    show ({A} : Finset (F × F)) = {(A.1, A.2)} by simp,
    W.veluDeficit_singleton_mul_pow_four_eq hP (hSeq A hA) (hav A hA)]
  simp only [eval_mul, eval_C, eval_pow, eval_prod, eval_sub, eval_X,
    eval_veluDeficitPsiCofactorReducedPoly]
  ring

theorem veluDeficitSingletonSumClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitSingletonSumClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_)
  refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
  have hcard : (S.erase A).card = S.card - 1 := Finset.card_erase_of_mem hA
  calc (C ((W.Ψ₃).eval A.1) * W.veluDeficitPsiCofactorReducedPoly A.1
          * (∏ B ∈ S.erase A, (X - C B.1)) ^ 4).natDegree
      ≤ (C ((W.Ψ₃).eval A.1) * W.veluDeficitPsiCofactorReducedPoly A.1).natDegree
          + ((∏ B ∈ S.erase A, ((X : F[X]) - C B.1)) ^ 4).natDegree := natDegree_mul_le
    _ ≤ 3 + 4 * (S.card - 1) := by
        refine add_le_add ((natDegree_C_mul_le _ _).trans
            (W.veluDeficitPsiCofactorReducedPoly_natDegree_le A.1)) ?_
        rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, hcard, le_refl]
    _ ≤ 4 * S.card - 1 := by omega

theorem veluDeficit_mul_prodPow_eq_clearedPoly_add_crossQuad {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (hav : ∀ A ∈ S, r ≠ A.1) :
    W.veluDeficit S r s * (∏ A ∈ S, (r - A.1)) ^ 4
      = (W.veluDeficitSingletonSumClearedPoly S).eval r
        + W.veluDeficitCrossQuad S r s * (∏ A ∈ S, (r - A.1)) ^ 4 := by
  rw [W.veluDeficit_eq_sum_singleton_add_crossQuad hP, add_mul,
    W.veluDeficit_sum_singleton_mul_prodPow_eq hP hSeq hav]

end ClearedPoly

section ArchetypeGeneralD

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_isConstant_constant_eq_zero_of_crossQuadProdDegLt [Infinite F]
    {S : Finset (F × F)} (hS : S.Nonempty) {c : F}
    (hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2)
    (habs : ∀ r : F, ∃ s, W.toAffine.Equation r s)
    (hc : ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ A ∈ S, r ≠ A.1) →
      W.veluDeficit S r s = c)
    {M : F[X]} (hMdeg : M.natDegree < 4 * S.card)
    (hM : ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ A ∈ S, r ≠ A.1) →
      W.veluDeficitCrossQuad S r s * (∏ A ∈ S, (r - A.1)) ^ 4 = M.eval r) :
    c = 0 := by
  classical
  set D : F[X] := veluKernelDenom S with hD_def
  set P : F[X] := C c * D ^ 4 - W.veluDeficitSingletonSumClearedPoly S - M with hP_def
  have hroot : ∀ r ∈ ((S.image Prod.fst : Finset F) : Set F)ᶜ, P.IsRoot r := by
    intro r hr
    have hav : ∀ A ∈ S, r ≠ A.1 := by
      intro A hA hrA; apply hr
      exact Finset.mem_coe.mpr (hrA ▸ Finset.mem_image_of_mem Prod.fst hA)
    obtain ⟨s, hrs⟩ := habs r
    have key := W.veluDeficit_mul_prodPow_eq_clearedPoly_add_crossQuad hrs hSeq hav
    rw [hc hrs hav, hM hrs hav] at key
    simp only [IsRoot, hP_def, hD_def, eval_sub, eval_mul, eval_C, eval_pow,
      eval_veluKernelDenom]
    linear_combination key
  have hinf : (((S.image Prod.fst : Finset F) : Set F)ᶜ).Infinite :=
    (Set.Finite.infinite_compl (Finset.finite_toSet _))
  have hP0 : P = 0 := eq_zero_of_infinite_isRoot P (hinf.mono fun r hr => hroot r hr)
  have hDmon : (D ^ 4).Monic := (veluKernelDenom_monic S).pow 4
  have hDdeg : (D ^ 4).natDegree = 4 * S.card := by
    rw [natDegree_pow, hD_def, veluKernelDenom_natDegree]
  have hcoeff : P.coeff (4 * S.card) = c := by
    rw [hP_def, coeff_sub, coeff_sub, coeff_C_mul]
    have h1 : (D ^ 4).coeff (4 * S.card) = 1 := by
      have := hDmon.coeff_natDegree; rwa [hDdeg] at this
    have h2 : (W.veluDeficitSingletonSumClearedPoly S).coeff (4 * S.card) = 0 :=
      coeff_eq_zero_of_natDegree_lt (W.veluDeficitSingletonSumClearedPoly_natDegree_lt hS)
    have h3 : M.coeff (4 * S.card) = 0 := coeff_eq_zero_of_natDegree_lt hMdeg
    rw [h1, h2, h3, mul_one, sub_zero, sub_zero]
  rw [hP0, coeff_zero] at hcoeff
  exact hcoeff.symm

end ArchetypeGeneralD

section CrossQuadCarrier

variable (F : Type*) [Field F] [DecidableEq F]

/-- After clearing fourth powers of the kernel denominators, the cross residual is a polynomial
of degree less than four times the summing-set length. -/
@[expose] public def VeluDeficitCrossQuadProdDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuad
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r

variable {F}

omit [DecidableEq F] in
theorem Affine.exists_equation_of_isAlgClosed [IsAlgClosed F] (W : WeierstrassCurve F)
    (r : F) : ∃ s, W.toAffine.Equation r s := by
  set q : F[X] := X ^ 2 + C (W.a₁ * r + W.a₃) * X
    - C (r ^ 3 + W.a₂ * r ^ 2 + W.a₄ * r + W.a₆) with hq
  have hqdeg : q.degree = 2 := by rw [hq]; compute_degree!
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_root q (by rw [hqdeg]; exact two_ne_zero)
  refine ⟨s, (Affine.equation_iff ..).mpr ?_⟩
  have hs' : q.eval s = 0 := hs
  simp only [hq, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hs'
  linear_combination hs'

end CrossQuadCarrier

end WeierstrassCurve

end

section

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

theorem exists_eq_algebraMap_of_forall_ord_nonneg₀ (v₀ : Place K F) (hdeg : v₀.deg = 1)
    {g : F} (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, (algebraMap K F).map_zero.symm⟩
  · exact eq_algebraMap_of_forall_ord_nonneg v₀ (v₀.isRational_of_deg_eq_one hdeg)
      (hdeg ▸ one_ne_zero) hg hord

end Place
end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

public theorem functionField_liouville_of_equation [HasPrincipalDivisors F W.FunctionField]
    [IsDedekindDomain W.CoordinateRing] {x₀ y₀ : F} (h₀ : W.Equation x₀ y₀)
    {f : W.FunctionField}
    (hord : ∀ v : AlgebraicCurve.Place F W.FunctionField, 0 ≤ v.ord f) :
    ∃ c : F, f = algebraMap F W.FunctionField c :=
  AlgebraicCurve.Place.exists_eq_algebraMap_of_forall_ord_nonneg₀
    (placeOfEquation h₀) (deg_placeOfEquation h₀) hord

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
section LiouvilleCarriers

variable (F : Type*) [Field F] [DecidableEq F]

/-- The cyclic-kernel residual at the generic point has nonnegative order at every function-field
place. -/
@[expose] public def VeluDeficitFunOrdNonnegAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ v : Place F W.toAffine.FunctionField,
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

/-- If the generic cyclic-kernel residual is a scalar, its value at every allowed curve point is
that same scalar. -/
@[expose] public def VeluDeficitFunSpecializesConstAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ c : F, W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2))
              = algebraMap F W.toAffine.FunctionField c →
        ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
          W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s = c

end LiouvilleCarriers

section LiouvilleBridge

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitIsConstantAt_of_ordNonneg_of_specializesConst' {p : ℕ}
    (hPD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      HasPrincipalDivisors F W.toAffine.FunctionField)
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      IsDedekindDomain W.toAffine.CoordinateRing)
    (hreg : VeluDeficitFunOrdNonnegAt F p)
    (hspec : VeluDeficitFunSpecializesConstAt F p) :
    VeluDeficitIsConstantAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have := hPD W hΔ
  have := hDD W hΔ
  obtain ⟨c, hc⟩ := Affine.functionField_liouville_of_equation h₀.left
    (hreg W hΔ x₀ y₀ h₀ hord)
  exact ⟨c, fun r s hrs hav => hspec W hΔ x₀ y₀ h₀ hord c hc hrs hav⟩

end LiouvilleBridge

end WeierstrassCurve

end

section

section

open scoped Pointwise

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_smul_iff_symm_mem (σ : F ≃ₐ[K] F) (v : Place K F) (f : F) :
    f ∈ (σ • v).toValuationSubring ↔ σ.symm f ∈ v.toValuationSubring := by
  rw [smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.smul_def, AlgEquiv.aut_inv]

end Place
end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

section TransportEngine

theorem isFinitePlace_smul_iff_forall_symm_mem (σ : W.FunctionField ≃ₐ[F] W.FunctionField)
    (v : AlgebraicCurve.Place F W.FunctionField) :
    IsFinitePlace (σ • v) ↔
      ∀ r : W.CoordinateRing,
        σ.symm (algebraMap W.CoordinateRing W.FunctionField r) ∈ v.toValuationSubring := by
  unfold IsFinitePlace
  exact forall_congr' fun r => Place.mem_smul_iff_symm_mem σ v _

theorem not_isFinitePlace_smul_of_symm_X_notMem
    (σ : W.FunctionField ≃ₐ[F] W.FunctionField) (v : AlgebraicCurve.Place F W.FunctionField)
    (h : σ.symm (polyToFunctionField W X) ∉ v.toValuationSubring) :
    ¬ IsFinitePlace (σ • v) := by
  rw [isFinitePlace_smul_iff_forall_symm_mem]
  intro hall
  apply h
  have := hall (algebraMap F[X] W.CoordinateRing X)
  rwa [← polyToFunctionField_apply] at this

end TransportEngine

section NonDegeneracy

variable (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

include hΔ hA in
theorem addXFun_ne_algebraMap : W.addXFun a b ≠ ι a := by
  classical
  intro hX
  have hY : W.addYFun a b = ι (W.negY a b) := by
    have heq := equation_map_addFun W hA
    rw [hX] at heq
    rcases Affine.Y_eq_of_X_eq heq (hA.map ι) rfl with hY | hY
    · exact absurd ⟨hX, hY⟩ (addFun_ne_mapPoint hΔ hA)
    · rw [hY, map_negY]
  have hcancel := addFun_neg_cancel_X hΔ hA
  rw [hX, hY] at hcancel
  rw [Affine.map_slope ι a a (W.negY a b) (W.negY a b),
    Affine.map_addX (W' := W) ι a a (W.slope a a (W.negY a b) (W.negY a b))] at hcancel
  exact polyToFunctionField_X_ne_algebraMap _ hcancel.symm

end NonDegeneracy

end Affine
end WeierstrassCurve

end

end

section

noncomputable section

namespace WeierstrassCurve
section Parity

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficit_negY (S : Finset (F × F)) (r s : F) :
    W.veluDeficit S r (W.toAffine.negY r s) = W.veluDeficit S r s := by
  unfold veluDeficit
  rw [W.veluY_negY]
  simp only [Affine.negY, veluQuotient_a₁, veluQuotient_a₃]
  ring

theorem veluDeficit_sum_singleton_negY (S : Finset (F × F)) (r s : F) :
    (∑ A ∈ S, W.veluDeficit {A} r (W.toAffine.negY r s))
      = ∑ A ∈ S, W.veluDeficit {A} r s :=
  Finset.sum_congr rfl fun A _ => W.veluDeficit_negY {A} r s

theorem veluDeficitCrossQuad_negY_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficitCrossQuad S r (W.toAffine.negY r s) = W.veluDeficitCrossQuad S r s := by
  have hP' : W.toAffine.Equation r (W.toAffine.negY r s) := (Affine.equation_neg r s).mpr hP
  have key := W.veluDeficit_eq_sum_singleton_add_crossQuad (S := S) hP'
  rw [W.veluDeficit_negY, W.veluDeficit_sum_singleton_negY,
    W.veluDeficit_eq_sum_singleton_add_crossQuad hP] at key
  exact (add_left_cancel key).symm

end Parity

section AlphaPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
def veluXCorrNumPoly (A : F × F) : F[X] :=
  C (W.veluT A.1 A.2) * (X - C A.1) + C (W.veluU A.1 A.2)

omit [DecidableEq F] in
lemma veluXCorrNumPoly_natDegree_le (A : F × F) :
    (W.veluXCorrNumPoly A).natDegree ≤ 1 := by
  unfold veluXCorrNumPoly; compute_degree

def veluXCorrPadPoly (S : Finset (F × F)) (A : F × F) : F[X] :=
  W.veluXCorrNumPoly A * (∏ B ∈ S.erase A, (X - C B.1)) ^ 2

theorem eval_veluXCorrPadPoly {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluX {A} r - r) * (∏ B ∈ S, (r - B.1)) ^ 2
      = (W.veluXCorrPadPoly S A).eval r := by
  have hd : r - A.1 ≠ 0 := sub_ne_zero.mpr (hav A hA)
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 2
      = (r - A.1) ^ 2 * (∏ B ∈ S.erase A, (r - B.1)) ^ 2 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, ← mul_assoc, veluXCorrPadPoly, veluXCorrNumPoly]
  simp only [veluX, Finset.sum_singleton, eval_mul, eval_add, eval_C, eval_sub, eval_X,
    eval_pow, eval_prod]
  field_simp
  ring

def veluXCorrSumPadPoly (S : Finset (F × F)) : F[X] := ∑ A ∈ S, W.veluXCorrPadPoly S A

omit [DecidableEq F] in
lemma veluX_sub_self_eq_sum_singleton (S : Finset (F × F)) (r : F) :
    W.veluX S r - r = ∑ A ∈ S, (W.veluX {A} r - r) := by
  simp only [veluX, Finset.sum_singleton, add_sub_cancel_left]

theorem eval_veluXCorrSumPadPoly {S : Finset (F × F)} {r : F} (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluX S r - r) * (∏ B ∈ S, (r - B.1)) ^ 2
      = (W.veluXCorrSumPadPoly S).eval r := by
  rw [veluXCorrSumPadPoly, eval_finsetSum, W.veluX_sub_self_eq_sum_singleton, Finset.sum_mul]
  exact Finset.sum_congr rfl fun A hA => W.eval_veluXCorrPadPoly hA hav

theorem veluXCorrPadPoly_natDegree_le {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) :
    (W.veluXCorrPadPoly S A).natDegree ≤ 2 * S.card - 1 := by
  have hScard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨A, hA⟩
  unfold veluXCorrPadPoly
  calc (W.veluXCorrNumPoly A * (∏ B ∈ S.erase A, ((X : F[X]) - C B.1)) ^ 2).natDegree
      ≤ 1 + 2 * (S.card - 1) := by
        refine natDegree_mul_le.trans (add_le_add (W.veluXCorrNumPoly_natDegree_le A) ?_)
        rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
        simp [Finset.card_erase_of_mem hA]
    _ ≤ 2 * S.card - 1 := by omega

theorem veluXCorrSumPadPoly_natDegree_le (S : Finset (F × F)) :
    (W.veluXCorrSumPadPoly S).natDegree ≤ 2 * S.card - 1 := by
  refine natDegree_le_iff_degree_le.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
  exact degree_le_natDegree.trans (Nat.cast_le.mpr (W.veluXCorrPadPoly_natDegree_le hA))

end AlphaPoly

section AlphaSqCross

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The cross residual from the quadratic `x`-correction and its coupling with the total Vélu
coefficient sum. -/
@[expose] public def veluDeficitCrossQuadAlphaSq (S : Finset (F × F)) (r : F) : F :=
  (-(3 * r + W.a₂) * (W.veluX S r - r) ^ 2 + 5 * W.veluTSum S * (W.veluX S r - r))
    - ∑ A ∈ S, (-(3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2
        + 5 * W.veluTSum {A} * (W.veluX {A} r - r))

/-- The cross residual remaining after removing the quadratic `x`-correction component. -/
@[expose] public def veluDeficitCrossQuadCubeBeta (S : Finset (F × F)) (r s : F) : F :=
  W.veluDeficitCrossQuad S r s - W.veluDeficitCrossQuadAlphaSq S r

omit [DecidableEq F] in
lemma veluDeficitCrossQuad_eq_alphaSq_add_cubeBeta (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuad S r s
      = W.veluDeficitCrossQuadAlphaSq S r + W.veluDeficitCrossQuadCubeBeta S r s := by
  unfold veluDeficitCrossQuadCubeBeta; ring

def veluDeficitCrossQuadAlphaSqClearedPoly (S : Finset (F × F)) : F[X] :=
  -(C 3 * X + C W.a₂)
      * ((W.veluXCorrSumPadPoly S) ^ 2 - ∑ A ∈ S, (W.veluXCorrPadPoly S A) ^ 2)
    + C 5 * (C (W.veluTSum S) * W.veluXCorrSumPadPoly S
        - ∑ A ∈ S, C (W.veluT A.1 A.2) * W.veluXCorrPadPoly S A)
      * (veluKernelDenom S) ^ 2

theorem veluDeficitCrossQuadAlphaSq_mul_prodPow_eq {S : Finset (F × F)} {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadAlphaSq S r * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadAlphaSqClearedPoly S).eval r := by
  set D : F := ∏ B ∈ S, (r - B.1)
  have hD4 : D ^ 4 = D ^ 2 * D ^ 2 := by ring
  have hαS : (W.veluX S r - r) * D ^ 2 = (W.veluXCorrSumPadPoly S).eval r :=
    W.eval_veluXCorrSumPadPoly hav
  have hαA : ∀ A ∈ S, (W.veluX {A} r - r) * D ^ 2 = (W.veluXCorrPadPoly S A).eval r :=
    fun A hA => W.eval_veluXCorrPadPoly hA hav
  unfold veluDeficitCrossQuadAlphaSq veluDeficitCrossQuadAlphaSqClearedPoly
  simp only [eval_add, eval_neg, eval_mul, eval_C, eval_X, eval_sub, eval_pow,
    eval_finsetSum, eval_veluKernelDenom]
  rw [sub_mul, Finset.sum_mul, hD4]
  have key1 : (-(3 * r + W.a₂) * (W.veluX S r - r) ^ 2
      + 5 * W.veluTSum S * (W.veluX S r - r)) * (D ^ 2 * D ^ 2)
      = -(3 * r + W.a₂) * ((W.veluXCorrSumPadPoly S).eval r) ^ 2
        + 5 * (W.veluTSum S * (W.veluXCorrSumPadPoly S).eval r) * D ^ 2 := by
    rw [← hαS]; ring
  have key2 : ∀ A ∈ S,
      (-(3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2
        + 5 * W.veluTSum {A} * (W.veluX {A} r - r)) * (D ^ 2 * D ^ 2)
      = -(3 * r + W.a₂) * ((W.veluXCorrPadPoly S A).eval r) ^ 2
        + 5 * (W.veluT A.1 A.2 * (W.veluXCorrPadPoly S A).eval r) * D ^ 2 := by
    intro A hA
    rw [← hαA A hA, veluTSum, Finset.sum_singleton]; ring
  rw [key1, Finset.sum_congr rfl key2, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem veluDeficitCrossQuadAlphaSqClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadAlphaSqClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  unfold veluDeficitCrossQuadAlphaSqClearedPoly
  refine (degree_add_le _ _).trans (max_le ?_ ?_)
  · rw [neg_mul, degree_neg]
    refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
    refine natDegree_mul_le.trans ?_
    have h1 : (C (3 : F) * X + C W.a₂).natDegree ≤ 1 := by compute_degree
    have h2 : ((W.veluXCorrSumPadPoly S) ^ 2
        - ∑ A ∈ S, (W.veluXCorrPadPoly S A) ^ 2).natDegree ≤ 2 * (2 * S.card - 1) := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_pow_le).trans
          (Nat.mul_le_mul_left 2 (W.veluXCorrSumPadPoly_natDegree_le S))
      · refine natDegree_le_iff_degree_le.mpr
          ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
        refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
        exact (natDegree_pow_le).trans
          (Nat.mul_le_mul_left 2 (W.veluXCorrPadPoly_natDegree_le hA))
    omega
  · refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
    refine natDegree_mul_le.trans ?_
    have hD : ((veluKernelDenom (F := F) S) ^ 2).natDegree = 2 * S.card := by
      rw [natDegree_pow, veluKernelDenom_natDegree]
    rw [hD]
    have hαbound : (C (5 : F) * (C (W.veluTSum S) * W.veluXCorrSumPadPoly S
        - ∑ A ∈ S, C (W.veluT A.1 A.2) * W.veluXCorrPadPoly S A)).natDegree
        ≤ 2 * S.card - 1 := by
      refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
      · exact (natDegree_C_mul_le _ _).trans (W.veluXCorrSumPadPoly_natDegree_le S)
      · refine natDegree_le_iff_degree_le.mpr
          ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
        exact degree_le_natDegree.trans (Nat.cast_le.mpr
          ((natDegree_C_mul_le _ _).trans (W.veluXCorrPadPoly_natDegree_le hA)))
    omega

end AlphaSqCross

section Reduction

variable (F : Type*) [Field F] [DecidableEq F]

/-- After clearing fourth-power kernel denominators, the cubic-and-`y` cross residual has
polynomial degree below four times the summing-set length. -/
@[expose] public def VeluDeficitCrossQuadCubeBetaDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadCubeBeta
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r

end Reduction

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

theorem forall_place_ord_nonneg_iff_finite_and_not_finite (g : W.FunctionField) :
    (∀ v : Place F W.FunctionField, 0 ≤ v.ord g)
      ↔ (∀ v : Place F W.FunctionField, IsFinitePlace v → 0 ≤ v.ord g)
        ∧ (∀ v : Place F W.FunctionField, ¬ IsFinitePlace v → 0 ≤ v.ord g) := by
  constructor
  · exact fun h => ⟨fun v _ => h v, fun v _ => h v⟩
  · rintro ⟨hfin, hinf⟩ v
    by_cases hv : IsFinitePlace v
    · exact hfin v hv
    · exact hinf v hv

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
section BinaryCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunOrdNonnegAtInftyAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ v : Place F W.toAffine.FunctionField, ¬ IsFinitePlace v →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

def VeluDeficitFunOrdNonnegAtFiniteAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ v : Place F W.toAffine.FunctionField, IsFinitePlace v →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

end BinaryCarriers

section BinaryRecombination

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAt_iff_atFinite_and_atInfty {p : ℕ} :
    VeluDeficitFunOrdNonnegAt F p
      ↔ VeluDeficitFunOrdNonnegAtFiniteAt F p ∧ VeluDeficitFunOrdNonnegAtInftyAt F p := by
  constructor
  · exact fun h => ⟨fun W hΔ x₀ y₀ h₀ hord v _ => h W hΔ x₀ y₀ h₀ hord v,
      fun W hΔ x₀ y₀ h₀ hord v _ => h W hΔ x₀ y₀ h₀ hord v⟩
  · rintro ⟨hfin, hinf⟩ W hΔ x₀ y₀ h₀ hord v
    exact ((Affine.forall_place_ord_nonneg_iff_finite_and_not_finite _).mpr
      ⟨hfin W hΔ x₀ y₀ h₀ hord, hinf W hΔ x₀ y₀ h₀ hord⟩) v

theorem veluDeficitFunOrdNonnegAt_of_atFinite_of_atInfty {p : ℕ}
    (hfin : VeluDeficitFunOrdNonnegAtFiniteAt F p)
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p) :
    VeluDeficitFunOrdNonnegAt F p :=
  (veluDeficitFunOrdNonnegAt_iff_atFinite_and_atInfty F).mpr ⟨hfin, hinf⟩

end BinaryRecombination

section KernelCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunOrdNonnegAtKernelAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

def VeluDeficitFunOrdNonnegOffKernelAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∉ hv.centre) →
          0 ≤ v.ord (W.toAffine.veluDeficitFun
            (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))

theorem veluDeficitFunOrdNonnegAtFiniteAt_of_atKernel_of_offKernel {p : ℕ}
    (hker : VeluDeficitFunOrdNonnegAtKernelAt F p)
    (hoff : VeluDeficitFunOrdNonnegOffKernelAt F p) :
    VeluDeficitFunOrdNonnegAtFiniteAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv
  by_cases hk : ∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
      XClass W.toAffine A.1 ∈ hv.centre
  · exact hker W hΔ x₀ y₀ h₀ hord v hv hk
  · exact hoff W hΔ x₀ y₀ h₀ hord v hv (fun A hA hmem => hk ⟨A, hA, hmem⟩)

end KernelCarriers

section TrichotomyRecombination

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAt_of_atInfty_of_atKernel_of_offKernel {p : ℕ}
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p)
    (hker : VeluDeficitFunOrdNonnegAtKernelAt F p)
    (hoff : VeluDeficitFunOrdNonnegOffKernelAt F p) :
    VeluDeficitFunOrdNonnegAt F p :=
  veluDeficitFunOrdNonnegAt_of_atFinite_of_atInfty F
    (veluDeficitFunOrdNonnegAtFiniteAt_of_atKernel_of_offKernel F hker hoff) hinf

end TrichotomyRecombination

end WeierstrassCurve

end

section

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

@[scoped simp]
theorem evalAt_zero : v.evalAt (0 : F) = 0 := by
  rw [← (algebraMap K F).map_zero, v.evalAt_algebraMap]

end Place
end AlgebraicCurve

namespace WeierstrassCurve
section ResidueCarrier

variable (F : Type*) [Field F] [DecidableEq F]

/-- Evaluating the generic cyclic-kernel residual at the place of an allowed affine point gives
the residual computed at its coordinates. -/
@[expose] public def VeluDeficitFunEvalAtPlaceAt
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0),
    letI := hDD W hΔ
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
      ∀ ⦃r s : F⦄ (hrs : W.toAffine.Equation r s),
        (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
        (placeOfEquation hrs).evalAt
            (W.toAffine.veluDeficitFun
              (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))
          = W.veluDeficit (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s

end ResidueCarrier

section ResidueBridge

variable {F : Type*} [Field F] [DecidableEq F]

public theorem veluDeficitFunSpecializesConstAt_of_evalAtPlace {p : ℕ}
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (heval : VeluDeficitFunEvalAtPlaceAt F hDD p) :
    VeluDeficitFunSpecializesConstAt F p := by
  intro W hΔ x₀ y₀ h₀ hord c hc r s hrs hav
  have := hDD W hΔ
  rw [← heval W hΔ x₀ y₀ h₀ hord hrs hav, hc, Place.evalAt_algebraMap]

end ResidueBridge

section Wire

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitIsConstantAt_of_ordNonneg_of_evalAtPlace {p : ℕ}
    (hPD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      HasPrincipalDivisors F W.toAffine.FunctionField)
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      IsDedekindDomain W.toAffine.CoordinateRing)
    (hreg : VeluDeficitFunOrdNonnegAt F p)
    (heval : VeluDeficitFunEvalAtPlaceAt F hDD p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_specializesConst' hPD hDD hreg
    (veluDeficitFunSpecializesConstAt_of_evalAtPlace hDD heval)

end Wire

end WeierstrassCurve

end

section

namespace WeierstrassCurve
section Constancy

variable {F : Type*} [Field F] [IsAlgClosed F]

public theorem kw_infinite_of_isAlgClosed : Infinite F := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have := Fintype.ofFinite F
  have hdeg : (∏ a : F, (X - C a) : F[X]).degree = (Fintype.card F : ℕ) := by
    simp [Polynomial.degree_prod, Polynomial.degree_X_sub_C]
  have hlt : (1 : F[X]).degree < (∏ a : F, (X - C a) : F[X]).degree := by
    rw [Polynomial.degree_one, hdeg]; exact_mod_cast Fintype.card_pos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (1 + ∏ a : F, (X - C a) : F[X])
    (by rw [Polynomial.degree_add_eq_right_of_degree_lt hlt, hdeg]
        exact_mod_cast Fintype.card_pos.ne')
  have heval : (1 + ∏ a : F, (X - C a) : F[X]).eval x = 1 := by
    simp only [eval_add, eval_one, eval_prod, eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_univ x) (sub_self x), add_zero]
  rw [Polynomial.IsRoot, heval] at hx
  exact one_ne_zero hx

public theorem kw_hDDTerm :
    ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing :=
  fun _W hΔ => Affine.CoordinateRing.isDedekindDomain_of_Δ_ne_zero hΔ

end Constancy

end WeierstrassCurve

end

section

noncomputable section

namespace WeierstrassCurve
section Helper

lemma cube_sum_sub_sum_cube_eq {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → R) :
    (∑ A ∈ s, f A) ^ 3 - ∑ A ∈ s, f A ^ 3
      = ∑ A ∈ s, ∑ B ∈ s.erase A, ((∑ E ∈ s, f E) + f A) * (f A * f B) := by
  have key : ∀ A ∈ s, ∑ B ∈ s.erase A, ((∑ E ∈ s, f E) + f A) * (f A * f B)
      = (∑ E ∈ s, f E) ^ 2 * f A - f A ^ 3 := by
    intro A hA
    have hsum : (∑ B ∈ s.erase A, f B) = (∑ E ∈ s, f E) - f A := by
      linear_combination Finset.add_sum_erase s f hA
    calc ∑ B ∈ s.erase A, ((∑ E ∈ s, f E) + f A) * (f A * f B)
        = ((∑ E ∈ s, f E) + f A) * f A * ∑ B ∈ s.erase A, f B := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun B _ => by ring
      _ = ((∑ E ∈ s, f E) + f A) * f A * ((∑ E ∈ s, f E) - f A) := by rw [hsum]
      _ = (∑ E ∈ s, f E) ^ 2 * f A - f A ^ 3 := by ring
  calc (∑ A ∈ s, f A) ^ 3 - ∑ A ∈ s, f A ^ 3
      = (∑ E ∈ s, f E) ^ 2 * (∑ A ∈ s, f A) - ∑ A ∈ s, f A ^ 3 := by ring
    _ = (∑ A ∈ s, (∑ E ∈ s, f E) ^ 2 * f A) - ∑ A ∈ s, f A ^ 3 := by rw [Finset.mul_sum]
    _ = ∑ A ∈ s, ((∑ E ∈ s, f E) ^ 2 * f A - f A ^ 3) := by rw [Finset.sum_sub_distrib]
    _ = _ := Eq.symm (Finset.sum_congr rfl key)

end Helper

section Decomp

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The cube of the total Vélu `x`-correction minus the sum of the cubes of the singleton
corrections. -/
@[expose] public def veluDeficitCrossQuadAlphaCube (S : Finset (F × F)) (r : F) : F :=
  (W.veluX S r - r) ^ 3 - ∑ A ∈ S, (W.veluX {A} r - r) ^ 3

/-- The cross residual remaining after removing both the quadratic and cubic contributions in the
`x`-correction. -/
@[expose] public def veluDeficitCrossQuadBetaOnly
    (S : Finset (F × F)) (r s : F) : F :=
  W.veluDeficitCrossQuadCubeBeta S r s + W.veluDeficitCrossQuadAlphaCube S r

lemma veluDeficitCrossQuadCubeBeta_eq_betaOnly_sub_alphaCube
    (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuadCubeBeta S r s
      = W.veluDeficitCrossQuadBetaOnly S r s - W.veluDeficitCrossQuadAlphaCube S r := by
  classical
  unfold veluDeficitCrossQuadBetaOnly; ring

theorem veluDeficitCrossQuadBetaOnly_eq (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuadBetaOnly S r s
      = ((W.veluY S r s - s) ^ 2 + W.a₁ * (W.veluX S r - r) * (W.veluY S r s - s))
        - ∑ A ∈ S, ((W.veluY {A} r s - s) ^ 2
            + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s)) := by
  classical
  unfold veluDeficitCrossQuadBetaOnly veluDeficitCrossQuadCubeBeta veluDeficitCrossQuadAlphaCube
    veluDeficitCrossQuad veluDeficitCrossQuadAlphaSq veluDeficitQuad
  have hsum : (∑ A ∈ S, ((W.veluY {A} r s - s) ^ 2
        + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s)
        - (3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2 - (W.veluX {A} r - r) ^ 3
        + 5 * W.veluTSum {A} * (W.veluX {A} r - r)))
      - (∑ A ∈ S, (-(3 * r + W.a₂) * (W.veluX {A} r - r) ^ 2
          + 5 * W.veluTSum {A} * (W.veluX {A} r - r)))
      + (∑ A ∈ S, (W.veluX {A} r - r) ^ 3)
      = ∑ A ∈ S, ((W.veluY {A} r s - s) ^ 2
          + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun A _ => by ring
  linear_combination -hsum

end Decomp

section PairPad

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluXCorrPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluXCorrNumPoly A * W.veluXCorrNumPoly B
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 2

theorem veluXCorrPadPoly_mul_eq_kernelDenom_sq_mul {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluXCorrPadPoly S A * W.veluXCorrPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluXCorrPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluXCorrPadPoly veluXCorrPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluXCorrPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluXCorrPairPadQuot S A B).natDegree ≤ 2 * S.card - 2 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  unfold veluXCorrPairPadQuot
  calc (W.veluXCorrNumPoly A * W.veluXCorrNumPoly B
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 2).natDegree
      ≤ (1 + 1) + 2 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · exact natDegree_mul_le.trans
            (add_le_add (W.veluXCorrNumPoly_natDegree_le A) (W.veluXCorrNumPoly_natDegree_le B))
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 2 * S.card - 2 := by
        have : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
        omega

end PairPad

section AlphaCubeCross

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaCubeClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A,
    (W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A) * W.veluXCorrPairPadQuot S A B

theorem veluXCorrSumPadPoly_cube_sub_sum_cube_eq (S : Finset (F × F)) :
    (W.veluXCorrSumPadPoly S) ^ 3 - ∑ A ∈ S, (W.veluXCorrPadPoly S A) ^ 3
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadAlphaCubeClearedPoly S := by
  have hRHS : (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadAlphaCubeClearedPoly S
      = ∑ A ∈ S, ∑ B ∈ S.erase A,
          (W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A)
            * (W.veluXCorrPadPoly S A * W.veluXCorrPadPoly S B) := by
    rw [veluDeficitCrossQuadAlphaCubeClearedPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun A hA => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
    rw [W.veluXCorrPadPoly_mul_eq_kernelDenom_sq_mul hA hBS hBA.symm]; ring
  rw [hRHS, veluXCorrSumPadPoly]
  exact cube_sum_sub_sum_cube_eq S _

theorem veluDeficitCrossQuadAlphaCube_mul_prodPow_eq {S : Finset (F × F)} {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadAlphaCube S r * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).eval r := by
  set D : F := ∏ B ∈ S, (r - B.1) with hD_def
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun B hB => sub_ne_zero.mpr (hav B hB)
  have hmul : W.veluDeficitCrossQuadAlphaCube S r * D ^ 6
      = D ^ 2 * (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).eval r := by
    have hαS := W.eval_veluXCorrSumPadPoly hav
    have hLHS : W.veluDeficitCrossQuadAlphaCube S r * D ^ 6
        = (W.veluXCorrSumPadPoly S).eval r ^ 3
          - ∑ A ∈ S, ((W.veluXCorrPadPoly S A).eval r) ^ 3 := by
      unfold veluDeficitCrossQuadAlphaCube
      rw [sub_mul, Finset.sum_mul,
        show (D : F) ^ 6 = (D ^ 2) ^ 3 from by ring, ← mul_pow, hαS]
      congr 1
      exact Finset.sum_congr rfl fun A hA => by
        rw [← mul_pow, W.eval_veluXCorrPadPoly hA hav]
    rw [hLHS]
    have hRHS := congrArg (Polynomial.eval r) (W.veluXCorrSumPadPoly_cube_sub_sum_cube_eq S)
    simpa only [eval_sub, eval_pow, eval_finsetSum, eval_mul, eval_veluKernelDenom,
      ← hD_def] using hRHS
  have h64 : D ^ 2 * (W.veluDeficitCrossQuadAlphaCube S r * D ^ 4)
      = D ^ 2 * (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).eval r := by
    rw [← hmul]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hD) h64

theorem veluDeficitCrossQuadAlphaCubeClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadAlphaCubeClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_)
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
  have h1 : (W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A).natDegree ≤ 2 * S.card - 1 :=
    (natDegree_add_le _ _).trans
      (max_le (W.veluXCorrSumPadPoly_natDegree_le S) (W.veluXCorrPadPoly_natDegree_le hA))
  have h2 := W.veluXCorrPairPadQuot_natDegree_le hA hBS hBA.symm
  calc ((W.veluXCorrSumPadPoly S + W.veluXCorrPadPoly S A)
          * W.veluXCorrPairPadQuot S A B).natDegree
      ≤ (2 * S.card - 1) + (2 * S.card - 2) := natDegree_mul_le.trans (add_le_add h1 h2)
    _ ≤ 4 * S.card - 1 := by omega

end AlphaCubeCross

section Reduction

variable (F : Type*) [Field F] [DecidableEq F]

/-- The cleared cross residual involving `y`-corrections is a polynomial in `x` of degree below
four times the summing-set length. -/
@[expose] public def VeluDeficitCrossQuadBetaOnlyDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadBetaOnly
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r

end Reduction

end WeierstrassCurve

end

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_smul_of_fixed (σ : F ≃ₐ[K] F) (v : Place K F) {g : F} (hg : σ g = g) :
    (σ • v).ord g = v.ord g := by
  conv_lhs => rw [← hg]
  exact ord_smul σ v g

theorem ord_nonneg_of_ord_smul_nonneg (σ : F ≃ₐ[K] F) (v : Place K F) {g : F}
    (hg : σ g = g) (h : 0 ≤ (σ • v).ord g) : 0 ≤ v.ord g :=
  (ord_smul_of_fixed σ v hg) ▸ h

end Place
end AlgebraicCurve

namespace WeierstrassCurve
section KernelTranslationCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunKernelTranslationAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          ∃ τ : W.toAffine.FunctionField ≃ₐ[F] W.toAffine.FunctionField,
            τ (W.toAffine.veluDeficitFun
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))
              = W.toAffine.veluDeficitFun
                  (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2))
            ∧ ¬ IsFinitePlace (τ • v)

end KernelTranslationCarrier

section KernelReduction

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAtKernelAt_of_kernelTranslation_of_atInfty {p : ℕ}
    (htr : VeluDeficitFunKernelTranslationAt F p)
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p) :
    VeluDeficitFunOrdNonnegAtKernelAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv hk
  obtain ⟨τ, hfix, hninf⟩ := htr W hΔ x₀ y₀ h₀ hord v hv hk
  exact Place.ord_nonneg_of_ord_smul_nonneg τ v hfix
    (hinf W hΔ x₀ y₀ h₀ hord (τ • v) hninf)

end KernelReduction

section Wire

variable {F : Type*} [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegAt_of_kernelTranslation_of_atInfty_of_offKernel {p : ℕ}
    (htr : VeluDeficitFunKernelTranslationAt F p)
    (hinf : VeluDeficitFunOrdNonnegAtInftyAt F p)
    (hoff : VeluDeficitFunOrdNonnegOffKernelAt F p) :
    VeluDeficitFunOrdNonnegAt F p :=
  veluDeficitFunOrdNonnegAt_of_atInfty_of_atKernel_of_offKernel F hinf
    (veluDeficitFunOrdNonnegAtKernelAt_of_kernelTranslation_of_atInfty F htr hinf) hoff

end Wire

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

theorem algebraMap_polynomial_X_sub_C (c : F) :
    algebraMap F[X] W.CoordinateRing (X - C c) = XClass W c := by
  rw [XClass, AdjoinRoot.algebraMap_eq]; rfl

theorem algebraMap_coordinateRing_XClass (c : F) :
    algebraMap W.CoordinateRing W.FunctionField (XClass W c)
      = polyToFunctionField W X - algebraMap F W.FunctionField c := by
  rw [← algebraMap_polynomial_X_sub_C, ← polyToFunctionField_apply, map_sub,
    polyToFunctionField_C]

theorem IsFinitePlace.inv_X_sub_const_mem_of_XClass_notMem_centre
    {v : Place F W.FunctionField} (hv : IsFinitePlace v) {c : F}
    (hc : XClass W c ∉ hv.centre) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹ ∈ v.toValuationSubring := by
  rw [← algebraMap_coordinateRing_XClass]
  exact hv.inv_mem hc

theorem IsFinitePlace.polyToFunctionField_X_mem {v : Place F W.FunctionField}
    (hv : IsFinitePlace v) : polyToFunctionField W X ∈ v.toValuationSubring := by
  rw [polyToFunctionField_apply]; exact hv _

theorem IsFinitePlace.yGen_mem {v : Place F W.FunctionField} (hv : IsFinitePlace v) :
    yGen W ∈ v.toValuationSubring := hv _

section OffKernelMembership

variable {v : Place F W.FunctionField} (hv : IsFinitePlace v) {S : Finset (F × F)}
  (hS : ∀ A ∈ S, XClass W A.1 ∉ hv.centre)

local notation "ι" => algebraMap F W.FunctionField
local notation "x" => polyToFunctionField W X
local notation "y" => yGen W
local notation "𝒪" => v.toValuationSubring

include hS in
theorem IsFinitePlace.veluX_liftSummingSet_mem_of_forall_XClass_notMem_centre :
    (W.map ι).veluX (W.liftSummingSet S) x ∈ 𝒪 := by
  unfold WeierstrassCurve.veluX WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  refine add_mem hv.polyToFunctionField_X_mem (Subring.sum_mem _ fun A hA => ?_)
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  have hδ : (x - ι A.1)⁻¹ ∈ 𝒪 :=
    hv.inv_X_sub_const_mem_of_XClass_notMem_centre (hS A hA)
  refine add_mem ?_ ?_
  · rw [div_eq_mul_inv]; exact mul_mem (v.algebraMap_mem' _) hδ
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (v.algebraMap_mem' _) (pow_mem hδ 2)

include hS in
theorem IsFinitePlace.veluY_liftSummingSet_mem_of_forall_XClass_notMem_centre :
    (W.map ι).veluY (W.liftSummingSet S) x y ∈ 𝒪 := by
  unfold WeierstrassCurve.veluY WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  refine sub_mem hv.yGen_mem (Subring.sum_mem _ fun A hA => ?_)
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  have hδ : (x - ι A.1)⁻¹ ∈ 𝒪 :=
    hv.inv_X_sub_const_mem_of_XClass_notMem_centre (hS A hA)
  have hx : x ∈ 𝒪 := hv.polyToFunctionField_X_mem
  have hy : y ∈ 𝒪 := hv.yGen_mem
  have hF : ∀ c : F, ι c ∈ 𝒪 := v.algebraMap_mem'
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _)
      (add_mem (add_mem (mul_mem (ofNat_mem 𝒪 2) hy) (mul_mem (hF _) hx)) (hF _)))
      (pow_mem hδ 3)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _)
      (sub_mem (add_mem (mul_mem (hF _) (sub_mem hx (hF _))) hy) (hF _))) (pow_mem hδ 2)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (sub_mem (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _))) (pow_mem hδ 2)

include hS in
theorem IsFinitePlace.veluDeficitFun_mem_of_forall_XClass_notMem_centre :
    W.veluDeficitFun S ∈ 𝒪 := by
  unfold WeierstrassCurve.veluDeficitFun WeierstrassCurve.veluDeficit
  set X' := (W.map ι).veluX (W.liftSummingSet S) x with hX'
  set Y' := (W.map ι).veluY (W.liftSummingSet S) x y with hY'
  have hXm : X' ∈ 𝒪 := hv.veluX_liftSummingSet_mem_of_forall_XClass_notMem_centre hS
  have hYm : Y' ∈ 𝒪 := hv.veluY_liftSummingSet_mem_of_forall_XClass_notMem_centre hS
  have hF : ∀ c : F, ι c ∈ 𝒪 := v.algebraMap_mem'
  rw [veluQuotient_a₄, veluQuotient_a₆,
    show (W.liftSummingSet S : Finset _) = S.map ⟨Prod.map ι ι, (RingHom.injective ι).prodMap
      (RingHom.injective ι)⟩ from rfl,
    map_veluTSum _ _ S (RingHom.injective ι), map_veluWSum _ _ S (RingHom.injective ι),
    map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_b₂]
  refine sub_mem (add_mem (add_mem (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm))
    (mul_mem (hF _) hYm)) ?_
  refine add_mem (add_mem (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)))
    (mul_mem ?_ hXm)) ?_
  · exact sub_mem (hF _) (mul_mem (ofNat_mem 𝒪 5) (hF _))
  · exact sub_mem (sub_mem (hF _) (mul_mem (hF _) (hF _))) (mul_mem (ofNat_mem 𝒪 7) (hF _))

end OffKernelMembership

theorem IsFinitePlace.ord_nonneg_veluDeficitFun_of_forall_XClass_notMem_centre
    {v : Place F W.FunctionField} (hv : IsFinitePlace v) {S : Finset (F × F)}
    (hS : ∀ A ∈ S, XClass W A.1 ∉ hv.centre) :
    0 ≤ v.ord (W.veluDeficitFun S) :=
  v.ord_nonneg_of_mem (hv.veluDeficitFun_mem_of_forall_XClass_notMem_centre hS)

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunOrdNonnegOffKernelAt (p : ℕ) : VeluDeficitFunOrdNonnegOffKernelAt F p :=
  fun _ _ _ _ _ _ _ hv hoff =>
    hv.ord_nonneg_veluDeficitFun_of_forall_XClass_notMem_centre hoff

end WeierstrassCurve

end

section

noncomputable section

namespace AlgebraicCurve
namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem evalAt_sum (hv : v.IsRational) {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ v.toValuationSubring) :
    v.evalAt (∑ i ∈ s, f i) = ∑ i ∈ s, v.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v.evalAt_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      v.evalAt_add hv (hf a (Finset.mem_insert_self a s))
        (Subring.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem evalAt_pow (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [v.evalAt_one]
  | succ n ih =>
    rw [pow_succ, v.evalAt_mul hv (pow_mem hf n) hf, ih, pow_succ]

theorem evalAt_natCast (n : ℕ) : v.evalAt (n : F) = n := by
  rw [show ((n : F) : F) = algebraMap K F n by push_cast; rfl, v.evalAt_algebraMap]

theorem evalAt_ofNat (n : ℕ) [n.AtLeastTwo] :
    v.evalAt (ofNat(n) : F) = ofNat(n) := by
  rw [← Nat.cast_ofNat, v.evalAt_natCast, Nat.cast_ofNat]

theorem evalAt_div' (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg0 : g ≠ 0) (hg : v.ord g = 0) :
    v.evalAt (f / g) = v.evalAt f / v.evalAt g := by
  have hginv : g⁻¹ ∈ v.toValuationSubring := v.mem_of_ord_nonneg (inv_ne_zero hg0)
    (by rw [v.ord_inv, hg]; exact le_of_eq (_root_.neg_zero).symm)
  rw [div_eq_mul_inv, v.evalAt_mul hv hf hginv, v.evalAt_inv hv hg0 hg, div_eq_mul_inv]

end Place
end AlgebraicCurve

namespace WeierstrassCurve
namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

section Atomic

variable [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)

public theorem isRational_placeOfEquation : (placeOfEquation hrs).IsRational :=
  (placeOfEquation hrs).isRational_of_deg_eq_one (deg_placeOfEquation hrs)

theorem evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal {z : W.CoordinateRing}
    (hz : z ∈ XYIdeal W r (C s)) :
    (placeOfEquation hrs).evalAt (algebraMap W.CoordinateRing W.FunctionField z) = 0 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [_root_.map_zero, Place.evalAt_zero]
  have hpos := (ord_placeOfEquation_pos_iff hrs hz0).mpr hz
  have hmem : algebraMap W.CoordinateRing W.FunctionField z
      ∈ (placeOfEquation hrs).toValuationSubring := isFinitePlace_placeOfEquation hrs z
  rw [(placeOfEquation hrs).evalAt_of_mem hmem]
  have hres : IsLocalRing.residue _
      (⟨algebraMap W.CoordinateRing W.FunctionField z, hmem⟩
        : (placeOfEquation hrs).toValuationSubring) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr
      (((placeOfEquation hrs).mem_maximalIdeal_iff_ord_pos
        (algebraMap_coordinateRing_ne_zero hz0) hmem).mpr hpos)
  rw [hres, ← _root_.map_zero (algebraMap F (placeOfEquation hrs).ResidueField),
    (placeOfEquation hrs).residueInv_algebraMap]

public theorem polyToFunctionField_X_mem_placeOfEquation :
    polyToFunctionField W X ∈ (placeOfEquation hrs).toValuationSubring := by
  rw [polyToFunctionField_apply]; exact isFinitePlace_placeOfEquation hrs _

public theorem yGen_mem_placeOfEquation :
    yGen W ∈ (placeOfEquation hrs).toValuationSubring :=
  isFinitePlace_placeOfEquation hrs _

include hrs in
theorem evalAt_polyToFunctionField_X_placeOfEquation :
    (placeOfEquation hrs).evalAt (polyToFunctionField W X) = r := by
  have hX : XClass W r ∈ XYIdeal W r (C s) := Ideal.subset_span (Set.mem_insert _ _)
  have h0 := evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal hrs hX
  have hbridge : algebraMap W.CoordinateRing W.FunctionField (XClass W r)
      = polyToFunctionField W X - algebraMap F W.FunctionField r := by
    rw [show XClass W r = algebraMap F[X] W.CoordinateRing (X - C r) from rfl,
      ← polyToFunctionField_apply, _root_.map_sub, polyToFunctionField_C]
  rw [hbridge, (placeOfEquation hrs).evalAt_sub (isRational_placeOfEquation hrs)
    (polyToFunctionField_X_mem_placeOfEquation hrs)
    ((placeOfEquation hrs).algebraMap_mem' r),
    Place.evalAt_algebraMap, sub_eq_zero] at h0
  exact h0

include hrs in
theorem evalAt_yGen_placeOfEquation :
    (placeOfEquation hrs).evalAt (yGen W) = s := by
  have hY : YClass W (C s) ∈ XYIdeal W r (C s) :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have h0 := evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal hrs hY
  have hbridge : algebraMap W.CoordinateRing W.FunctionField (YClass W (C s))
      = yGen W - algebraMap F W.FunctionField s := by
    rw [YClass, _root_.map_sub, _root_.map_sub, yGen]; congr 1
  rw [hbridge, (placeOfEquation hrs).evalAt_sub (isRational_placeOfEquation hrs)
    (yGen_mem_placeOfEquation hrs)
    ((placeOfEquation hrs).algebraMap_mem' s),
    Place.evalAt_algebraMap, sub_eq_zero] at h0
  exact h0

include hrs in
theorem evalAt_X_sub_const_placeOfEquation (c : F) :
    (placeOfEquation hrs).evalAt (polyToFunctionField W X - algebraMap F W.FunctionField c)
      = r - c := by
  rw [(placeOfEquation hrs).evalAt_sub (isRational_placeOfEquation hrs)
    (polyToFunctionField_X_mem_placeOfEquation hrs)
    ((placeOfEquation hrs).algebraMap_mem' c),
    evalAt_polyToFunctionField_X_placeOfEquation hrs, Place.evalAt_algebraMap]

include hrs in
public theorem ord_X_sub_const_placeOfEquation_of_ne {c : F} (hrc : r ≠ c) :
    (placeOfEquation hrs).ord (polyToFunctionField W X - algebraMap F W.FunctionField c) = 0 := by
  have hbridge : polyToFunctionField W X - algebraMap F W.FunctionField c
      = algebraMap W.CoordinateRing W.FunctionField (XClass W c) := by
    rw [show XClass W c = algebraMap F[X] W.CoordinateRing (X - C c) from rfl,
      ← polyToFunctionField_apply, _root_.map_sub, polyToFunctionField_C]
  rw [hbridge]
  refine le_antisymm ?_ (ord_placeOfEquation_nonneg hrs _)
  rw [show (0 : ℤ) = 0 from rfl, ← not_lt]
  intro hpos
  have hmem := (ord_placeOfEquation_pos_iff hrs (XClass_ne_zero c)).mp hpos
  rw [show XClass W c = CoordinateRing.mk W (C (X - C c)) from rfl,
    mk_mem_XYIdeal_iff hrs] at hmem
  simp only [evalEval_C, eval_sub, eval_X, eval_C, sub_eq_zero] at hmem
  exact hrc hmem

end Atomic

section VeluCoord

variable [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
  {S : Finset (F × F)}

lemma const_mem_placeOfEquation (c : F) :
    algebraMap F W.FunctionField c ∈ (placeOfEquation hrs).toValuationSubring :=
  (placeOfEquation hrs).algebraMap_mem' c

omit [IsDedekindDomain W.CoordinateRing] in
lemma X_sub_const_ne_zero (c : F) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c : W.FunctionField) ≠ 0 :=
  sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap c)

lemma inv_X_sub_const_mem_placeOfEquation {c : F} (hrc : r ≠ c) :
    (polyToFunctionField W X - algebraMap F W.FunctionField c)⁻¹
      ∈ (placeOfEquation hrs).toValuationSubring := by
  have hord := ord_X_sub_const_placeOfEquation_of_ne hrs hrc
  refine (placeOfEquation hrs).mem_of_ord_nonneg (inv_ne_zero (X_sub_const_ne_zero c)) ?_
  rw [(placeOfEquation hrs).ord_inv, hord]
  exact le_of_eq (_root_.neg_zero).symm

lemma veluX_summand_mem (A : F × F) (hrA : r ≠ A.1) :
    (algebraMap F W.FunctionField (W.veluT A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1)
      + algebraMap F W.FunctionField (W.veluU A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2)
      ∈ (placeOfEquation hrs).toValuationSubring := by
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs hrA
  refine add_mem ?_ ?_
  · rw [div_eq_mul_inv]; exact mul_mem (const_mem_placeOfEquation hrs _) hδ
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (const_mem_placeOfEquation hrs _) (pow_mem hδ 2)

include hrs in
public theorem evalAt_veluX_liftSummingSet_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (placeOfEquation hrs).evalAt
        ((W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
          (polyToFunctionField W X)) = W.veluX S r := by
  have hv := isRational_placeOfEquation hrs
  unfold WeierstrassCurve.veluX WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  rw [(placeOfEquation hrs).evalAt_add hv (polyToFunctionField_X_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => veluX_summand_mem hrs A (hS A hA)),
    evalAt_polyToFunctionField_X_placeOfEquation hrs,
    (placeOfEquation hrs).evalAt_sum hv _ _ (fun A hA => veluX_summand_mem hrs A (hS A hA))]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hδ0 := X_sub_const_ne_zero (W := W) A.1
  have hδord := ord_X_sub_const_placeOfEquation_of_ne hrs (hS A hA)
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs (hS A hA)
  have hδ2ord : (placeOfEquation hrs).ord
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2) = 0 := by
    have := (placeOfEquation hrs).ord_zpow
      (polyToFunctionField W X - algebraMap F W.FunctionField A.1) 2
    rw [zpow_two] at this
    rw [pow_two, this, hδord, mul_zero]
  have hm1 : (algebraMap F W.FunctionField (W.veluT A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1))
      ∈ (placeOfEquation hrs).toValuationSubring := by
    rw [div_eq_mul_inv]; exact mul_mem (const_mem_placeOfEquation hrs _) hδ
  have hm2 : (algebraMap F W.FunctionField (W.veluU A.1 A.2)
        / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2)
      ∈ (placeOfEquation hrs).toValuationSubring := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (const_mem_placeOfEquation hrs _) (pow_mem hδ 2)
  rw [(placeOfEquation hrs).evalAt_add hv hm1 hm2,
    (placeOfEquation hrs).evalAt_div' hv (const_mem_placeOfEquation hrs _) hδ0 hδord,
    (placeOfEquation hrs).evalAt_div' hv (const_mem_placeOfEquation hrs _)
      (pow_ne_zero 2 hδ0) hδ2ord,
    evalAt_X_sub_const_placeOfEquation hrs,
    (placeOfEquation hrs).evalAt_pow hv
      (sub_mem (polyToFunctionField_X_mem_placeOfEquation hrs)
        (const_mem_placeOfEquation hrs _)) 2,
    evalAt_X_sub_const_placeOfEquation hrs,
    Place.evalAt_algebraMap, Place.evalAt_algebraMap]

lemma veluX_liftSummingSet_mem_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
        (polyToFunctionField W X) ∈ (placeOfEquation hrs).toValuationSubring := by
  unfold WeierstrassCurve.veluX WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU]
  exact add_mem (polyToFunctionField_X_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => veluX_summand_mem hrs A (hS A hA))

lemma veluY_summand_mem (A : F × F) (hrA : r ≠ A.1) :
    (algebraMap F W.FunctionField (W.veluU A.1 A.2)
          * (2 * yGen W + algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
              + algebraMap F W.FunctionField W.a₃)
          / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 3
      + algebraMap F W.FunctionField (W.veluT A.1 A.2)
          * (algebraMap F W.FunctionField W.a₁
              * (polyToFunctionField W X - algebraMap F W.FunctionField A.1)
            + yGen W - algebraMap F W.FunctionField A.2)
          / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2
      + (algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField (W.veluU A.1 A.2)
          - algebraMap F W.FunctionField (W.veluGx A.1 A.2)
              * algebraMap F W.FunctionField (W.veluGy A.1 A.2))
          / (polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ 2)
      ∈ (placeOfEquation hrs).toValuationSubring := by
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs hrA
  have hX := polyToFunctionField_X_mem_placeOfEquation hrs
  have hY := yGen_mem_placeOfEquation hrs
  have hF := const_mem_placeOfEquation hrs
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _)
      (add_mem (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _)))
      (pow_mem hδ 3)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (mul_mem (hF _) (sub_mem (add_mem (mul_mem (hF _)
      (sub_mem hX (hF _))) hY) (hF _))) (pow_mem hδ 2)
  · rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (sub_mem (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _))) (pow_mem hδ 2)

lemma veluY_liftSummingSet_mem_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
        (polyToFunctionField W X) (yGen W) ∈ (placeOfEquation hrs).toValuationSubring := by
  unfold WeierstrassCurve.veluY WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  exact sub_mem (yGen_mem_placeOfEquation hrs)
    (Subring.sum_mem _ fun A hA => veluY_summand_mem hrs A (hS A hA))

include hrs in
public theorem evalAt_veluY_liftSummingSet_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (placeOfEquation hrs).evalAt
        ((W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
          (polyToFunctionField W X) (yGen W)) = W.veluY S r s := by
  have hv := isRational_placeOfEquation hrs
  have hX := polyToFunctionField_X_mem_placeOfEquation hrs
  have hY := yGen_mem_placeOfEquation hrs
  have hF := const_mem_placeOfEquation hrs
  unfold WeierstrassCurve.veluY WeierstrassCurve.liftSummingSet
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT, map_veluU,
    map_veluGx, map_veluGy, map_a₁, map_a₃]
  rw [(placeOfEquation hrs).evalAt_sub hv hY
      (Subring.sum_mem _ fun A hA => veluY_summand_mem hrs A (hS A hA)),
    evalAt_yGen_placeOfEquation hrs,
    (placeOfEquation hrs).evalAt_sum hv _ _ (fun A hA => veluY_summand_mem hrs A (hS A hA))]
  congr 1
  refine Finset.sum_congr rfl fun A hA => ?_
  have hδ0 := X_sub_const_ne_zero (W := W) A.1
  have hδord := ord_X_sub_const_placeOfEquation_of_ne hrs (hS A hA)
  have hδ := inv_X_sub_const_mem_placeOfEquation hrs (hS A hA)
  have hδpowmem : ∀ n : ℕ,
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ n)⁻¹
        ∈ (placeOfEquation hrs).toValuationSubring :=
    fun n => by rw [← inv_pow]; exact pow_mem hδ n
  have hδpow : ∀ n : ℕ, (placeOfEquation hrs).ord
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ n) = 0 := fun n => by
    have := (placeOfEquation hrs).ord_zpow
      (polyToFunctionField W X - algebraMap F W.FunctionField A.1) n
    rw [zpow_natCast] at this; rw [this, hδord, mul_zero]
  have hδeval := evalAt_X_sub_const_placeOfEquation hrs A.1
  have hδpoweval : ∀ n : ℕ, (placeOfEquation hrs).evalAt
      ((polyToFunctionField W X - algebraMap F W.FunctionField A.1) ^ n) = (r - A.1) ^ n :=
    fun n => by
      rw [(placeOfEquation hrs).evalAt_pow hv (sub_mem hX (hF _)) n, hδeval]
  have hN1 : (algebraMap F W.FunctionField (W.veluU A.1 A.2)
      * (2 * yGen W + algebraMap F W.FunctionField W.a₁ * polyToFunctionField W X
          + algebraMap F W.FunctionField W.a₃)) ∈ (placeOfEquation hrs).toValuationSubring :=
    mul_mem (hF _)
      (add_mem (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _))
  have hN2 : (algebraMap F W.FunctionField (W.veluT A.1 A.2)
      * (algebraMap F W.FunctionField W.a₁
          * (polyToFunctionField W X - algebraMap F W.FunctionField A.1)
        + yGen W - algebraMap F W.FunctionField A.2))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    mul_mem (hF _) (sub_mem (add_mem (mul_mem (hF _) (sub_mem hX (hF _))) hY) (hF _))
  have hN3 : (algebraMap F W.FunctionField W.a₁ * algebraMap F W.FunctionField (W.veluU A.1 A.2)
      - algebraMap F W.FunctionField (W.veluGx A.1 A.2)
          * algebraMap F W.FunctionField (W.veluGy A.1 A.2))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    sub_mem (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _))
  rw [(placeOfEquation hrs).evalAt_add hv
      (add_mem (by rw [div_eq_mul_inv]; exact mul_mem hN1 (hδpowmem 3))
        (by rw [div_eq_mul_inv]; exact mul_mem hN2 (hδpowmem 2)))
      (by rw [div_eq_mul_inv]; exact mul_mem hN3 (hδpowmem 2)),
    (placeOfEquation hrs).evalAt_add hv
      (by rw [div_eq_mul_inv]; exact mul_mem hN1 (hδpowmem 3))
      (by rw [div_eq_mul_inv]; exact mul_mem hN2 (hδpowmem 2)),
    (placeOfEquation hrs).evalAt_div' hv hN1 (pow_ne_zero 3 hδ0) (hδpow 3), hδpoweval 3,
    (placeOfEquation hrs).evalAt_div' hv hN2 (pow_ne_zero 2 hδ0) (hδpow 2), hδpoweval 2,
    (placeOfEquation hrs).evalAt_div' hv hN3 (pow_ne_zero 2 hδ0) (hδpow 2), hδpoweval 2]
  congr 2
  · rw [(placeOfEquation hrs).evalAt_mul hv (hF _)
        (add_mem (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _)),
      Place.evalAt_algebraMap,
      (placeOfEquation hrs).evalAt_add hv
        (add_mem (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX)) (hF _),
      (placeOfEquation hrs).evalAt_add hv (mul_mem (ofNat_mem _ 2) hY) (mul_mem (hF _) hX),
      (placeOfEquation hrs).evalAt_mul hv (ofNat_mem _ 2) hY,
      (placeOfEquation hrs).evalAt_mul hv (hF _) hX,
      (placeOfEquation hrs).evalAt_ofNat 2,
      evalAt_yGen_placeOfEquation hrs, evalAt_polyToFunctionField_X_placeOfEquation hrs,
      Place.evalAt_algebraMap, Place.evalAt_algebraMap]
  · rw [(placeOfEquation hrs).evalAt_mul hv (hF _)
        (sub_mem (add_mem (mul_mem (hF _) (sub_mem hX (hF _))) hY) (hF _)),
      Place.evalAt_algebraMap,
      (placeOfEquation hrs).evalAt_sub hv
        (add_mem (mul_mem (hF _) (sub_mem hX (hF _))) hY) (hF _),
      (placeOfEquation hrs).evalAt_add hv (mul_mem (hF _) (sub_mem hX (hF _))) hY,
      (placeOfEquation hrs).evalAt_mul hv (hF _) (sub_mem hX (hF _)),
      hδeval, evalAt_yGen_placeOfEquation hrs,
      Place.evalAt_algebraMap, Place.evalAt_algebraMap]
  · rw [(placeOfEquation hrs).evalAt_sub hv (mul_mem (hF _) (hF _)) (mul_mem (hF _) (hF _)),
      (placeOfEquation hrs).evalAt_mul hv (hF _) (hF _),
      (placeOfEquation hrs).evalAt_mul hv (hF _) (hF _),
      Place.evalAt_algebraMap, Place.evalAt_algebraMap, Place.evalAt_algebraMap,
      Place.evalAt_algebraMap]

end VeluCoord

section Discharge

variable [IsDedekindDomain W.CoordinateRing] {r s : F} (hrs : W.Equation r s)
  {S : Finset (F × F)}

include hrs in
theorem evalAt_veluDeficitFun_placeOfEquation (hS : ∀ A ∈ S, r ≠ A.1) :
    (placeOfEquation hrs).evalAt (W.veluDeficitFun S) = W.veluDeficit S r s := by
  have hv := isRational_placeOfEquation hrs
  unfold WeierstrassCurve.veluDeficitFun WeierstrassCurve.veluDeficit
  set X' := (W.map (algebraMap F W.FunctionField)).veluX (W.liftSummingSet S)
    (polyToFunctionField W X) with hX'
  set Y' := (W.map (algebraMap F W.FunctionField)).veluY (W.liftSummingSet S)
    (polyToFunctionField W X) (yGen W) with hY'
  have hXm : X' ∈ (placeOfEquation hrs).toValuationSubring :=
    veluX_liftSummingSet_mem_placeOfEquation hrs hS
  have hYm : Y' ∈ (placeOfEquation hrs).toValuationSubring :=
    veluY_liftSummingSet_mem_placeOfEquation hrs hS
  have hF : ∀ c : F, algebraMap F W.FunctionField c
      ∈ (placeOfEquation hrs).toValuationSubring :=
    (placeOfEquation hrs).algebraMap_mem'
  have hXe : (placeOfEquation hrs).evalAt X' = W.veluX S r :=
    evalAt_veluX_liftSummingSet_placeOfEquation hrs hS
  have hYe : (placeOfEquation hrs).evalAt Y' = W.veluY S r s :=
    evalAt_veluY_liftSummingSet_placeOfEquation hrs hS
  rw [veluQuotient_a₄, veluQuotient_a₆,
    show (W.liftSummingSet S : Finset _) = S.map ⟨Prod.map (algebraMap F W.FunctionField)
      (algebraMap F W.FunctionField), (RingHom.injective _).prodMap
      (RingHom.injective _)⟩ from rfl,
    map_veluTSum _ _ S (RingHom.injective _), map_veluWSum _ _ S (RingHom.injective _),
    map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_b₂]
  have hcoef4 : (algebraMap F W.FunctionField W.a₄
      - 5 * algebraMap F W.FunctionField (W.veluTSum S))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    sub_mem (hF _) (mul_mem (ofNat_mem _ 5) (hF _))
  have hcoef6 : (algebraMap F W.FunctionField W.a₆
      - algebraMap F W.FunctionField W.b₂ * algebraMap F W.FunctionField (W.veluTSum S)
      - 7 * algebraMap F W.FunctionField (W.veluWSum S))
      ∈ (placeOfEquation hrs).toValuationSubring :=
    sub_mem (sub_mem (hF _) (mul_mem (hF _) (hF _))) (mul_mem (ofNat_mem _ 7) (hF _))
  rw [(placeOfEquation hrs).evalAt_sub hv
      (add_mem (add_mem (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm))
        (mul_mem (hF _) hYm))
      (add_mem (add_mem (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)))
        (mul_mem hcoef4 hXm)) hcoef6),
    (placeOfEquation hrs).evalAt_add hv
      (add_mem (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm)) (mul_mem (hF _) hYm),
    (placeOfEquation hrs).evalAt_add hv (pow_mem hYm 2) (mul_mem (mul_mem (hF _) hXm) hYm),
    (placeOfEquation hrs).evalAt_pow hv hYm 2, hYe,
    (placeOfEquation hrs).evalAt_mul hv (mul_mem (hF _) hXm) hYm,
    (placeOfEquation hrs).evalAt_mul hv (hF _) hXm, Place.evalAt_algebraMap, hXe, hYe,
    (placeOfEquation hrs).evalAt_mul hv (hF _) hYm, Place.evalAt_algebraMap, hYe,
    (placeOfEquation hrs).evalAt_add hv
      (add_mem (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)))
        (mul_mem hcoef4 hXm)) hcoef6,
    (placeOfEquation hrs).evalAt_add hv
      (add_mem (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2))) (mul_mem hcoef4 hXm),
    (placeOfEquation hrs).evalAt_add hv (pow_mem hXm 3) (mul_mem (hF _) (pow_mem hXm 2)),
    (placeOfEquation hrs).evalAt_pow hv hXm 3, hXe,
    (placeOfEquation hrs).evalAt_mul hv (hF _) (pow_mem hXm 2),
    (placeOfEquation hrs).evalAt_pow hv hXm 2, hXe, Place.evalAt_algebraMap,
    (placeOfEquation hrs).evalAt_mul hv hcoef4 hXm,
    (placeOfEquation hrs).evalAt_sub hv (hF _) (mul_mem (ofNat_mem _ 5) (hF _)),
    (placeOfEquation hrs).evalAt_mul hv (ofNat_mem _ 5) (hF _),
    (placeOfEquation hrs).evalAt_ofNat 5, Place.evalAt_algebraMap, Place.evalAt_algebraMap, hXe,
    (placeOfEquation hrs).evalAt_sub hv (sub_mem (hF _) (mul_mem (hF _) (hF _)))
      (mul_mem (ofNat_mem _ 7) (hF _)),
    (placeOfEquation hrs).evalAt_sub hv (hF _) (mul_mem (hF _) (hF _)),
    (placeOfEquation hrs).evalAt_mul hv (hF _) (hF _),
    (placeOfEquation hrs).evalAt_mul hv (ofNat_mem _ 7) (hF _),
    (placeOfEquation hrs).evalAt_ofNat 7, Place.evalAt_algebraMap, Place.evalAt_algebraMap,
    Place.evalAt_algebraMap, Place.evalAt_algebraMap,
    veluQuotient_a₄, veluQuotient_a₆]

end Discharge

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
variable {F : Type*} [Field F] [DecidableEq F]

public theorem veluDeficitFunEvalAtPlaceAt
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    (p : ℕ) : VeluDeficitFunEvalAtPlaceAt F hDD p := by
  intro W hΔ x₀ y₀ h₀ _hord r s hrs hav
  have := hDD W hΔ
  exact Affine.evalAt_veluDeficitFun_placeOfEquation hrs hav

public theorem veluDeficitIsConstantAt_of_ordNonneg_of_dedekind {p : ℕ}
    (hPD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      HasPrincipalDivisors F W.toAffine.FunctionField)
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
      IsDedekindDomain W.toAffine.CoordinateRing)
    (hreg : VeluDeficitFunOrdNonnegAt F p) :
    VeluDeficitIsConstantAt F p :=
  veluDeficitIsConstantAt_of_ordNonneg_of_evalAtPlace hPD hDD hreg
    (veluDeficitFunEvalAtPlaceAt hDD p)

end WeierstrassCurve

end

section

noncomputable section

namespace WeierstrassCurve
section Psi2Sq

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem Ψ₂Sq_ne_zero_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) : W.Ψ₂Sq ≠ 0 := by
  intro h0
  apply hΔ
  have h4 : (4 : F) = 0 := by
    have hc := congrArg (·.coeff 3) h0
    simpa only [W.coeff_Ψ₂Sq, coeff_zero] using hc
  have hb₂ : W.b₂ = 0 := by
    have hc := congrArg (·.coeff 2) h0
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_zero, coeff_X,
      mul_ite, mul_one, mul_zero] at hc
    norm_num at hc
    exact hc
  have hb₆ : W.b₆ = 0 := by
    have hc := congrArg (·.coeff 0) h0
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_zero, coeff_X,
      mul_ite, mul_one, mul_zero] at hc
    norm_num at hc
    exact hc
  rw [WeierstrassCurve.Δ, hb₂, hb₆]
  linear_combination -(2 * W.b₄ ^ 3) * h4

end Psi2Sq

section Parity

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem veluDeficitCrossQuadBetaOnly_negY_of_equation {S : Finset (F × F)} {r s : F}
    (hP : W.toAffine.Equation r s) :
    W.veluDeficitCrossQuadBetaOnly S r (W.toAffine.negY r s)
      = W.veluDeficitCrossQuadBetaOnly S r s := by
  classical
  unfold veluDeficitCrossQuadBetaOnly veluDeficitCrossQuadCubeBeta
  rw [W.veluDeficitCrossQuad_negY_of_equation hP]

end Parity

section BetaSCoeffPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
def veluYCorrSCoeffNumPoly (A : F × F) : F[X] :=
  -(C (2 * W.veluU A.1 A.2) + C (W.veluT A.1 A.2) * (X - C A.1))

omit [DecidableEq F] in
lemma veluYCorrSCoeffNumPoly_natDegree_le (A : F × F) :
    (W.veluYCorrSCoeffNumPoly A).natDegree ≤ 1 := by
  unfold veluYCorrSCoeffNumPoly; compute_degree

def veluYCorrSCoeffPadPoly (S : Finset (F × F)) (A : F × F) : F[X] :=
  W.veluYCorrSCoeffNumPoly A * (∏ B ∈ S.erase A, (X - C B.1)) ^ 3

theorem eval_veluYCorrSCoeffPadPoly {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3 + W.veluT A.1 A.2 / (r - A.1) ^ 2)
        * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrSCoeffPadPoly S A).eval r := by
  have hd : r - A.1 ≠ 0 := sub_ne_zero.mpr (hav A hA)
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 3
      = (r - A.1) ^ 3 * (∏ B ∈ S.erase A, (r - B.1)) ^ 3 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, veluYCorrSCoeffPadPoly, veluYCorrSCoeffNumPoly]
  simp only [eval_mul, eval_neg, eval_add, eval_C, eval_sub, eval_X, eval_pow, eval_prod]
  field_simp

def veluYCorrSCoeffSumPadPoly (S : Finset (F × F)) : F[X] := ∑ A ∈ S, W.veluYCorrSCoeffPadPoly S A

omit [DecidableEq F] in
lemma veluY_sub_self_sLinear (S : Finset (F × F)) (r s : F) :
    (W.veluY S r s - s) - (W.veluY S r 0 - 0)
      = (∑ A ∈ S, -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * s := by
  simp only [veluY, sub_zero, sub_sub_cancel_left, zero_sub, sub_neg_eq_add, neg_add_eq_sub,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun A _ => by ring

omit [DecidableEq F] in
theorem veluY_singleton_sub_sLinear (A : F × F) (r s : F) :
    (W.veluY {A} r s - s) - (W.veluY {A} r 0 - 0)
      = -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3 + W.veluT A.1 A.2 / (r - A.1) ^ 2) * s := by
  have key := W.veluY_sub_self_sLinear {A} r s
  simpa using key

theorem veluY_sub_self_sCoeff_mul_prodPow_eq {S : Finset (F × F)} {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (∑ A ∈ S, -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrSCoeffSumPadPoly S).eval r := by
  rw [veluYCorrSCoeffSumPadPoly, eval_finsetSum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun A hA => W.eval_veluYCorrSCoeffPadPoly hA hav

end BetaSCoeffPoly

section Reduction

variable (F : Type*) [Field F] [DecidableEq F]

/-- The cleared `y`-correction cross residual is `M(x) + N(x)y`, with the degree of `M` below
four times the summing-set length. -/
@[expose] public def VeluDeficitCrossQuadBetaSDecompDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M N : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadBetaOnly
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r + N.eval r * s

end Reduction

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F]

section Transcendence

variable {W : Affine F} {a b : F}

theorem isIntegral_addYFun_adjoin_addXFun (hA : W.Equation a b) :
    IsIntegral (Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField)) (W.addYFun a b) := by
  set R := Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField)
  have hmem : ∀ p : F[X], (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom p ∈ R := by
    intro p
    change Polynomial.aeval (R := F) (W.addXFun a b) p ∈ R
    rw [show R = Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField) from rfl,
      Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  let φ : F[X] →+* R :=
    (Polynomial.aeval (R := F) (W.addXFun a b)).toRingHom.codRestrict R.toSubring hmem
  refine ⟨W.polynomial.map φ, monic_polynomial.map φ, ?_⟩
  change Polynomial.eval₂ (algebraMap R W.FunctionField) (W.addYFun a b) (W.polynomial.map φ) = 0
  rw [Polynomial.eval₂_map]
  exact eval₂_polynomial_addFun W hA

theorem addXFunTranscendental (hΔ : W.Δ ≠ 0) (hA : W.Equation a b) :
    AddXFunTranscendental W a b := by
  intro hX'alg
  have hX'int : _root_.IsIntegral F (W.addXFun a b) := isAlgebraic_iff_isIntegral.mp hX'alg
  have hRint : Algebra.IsIntegral F
      (Algebra.adjoin F ({W.addXFun a b} : Set W.FunctionField)) :=
    Algebra.IsIntegral.adjoin (fun x hx => by
      obtain rfl := Set.mem_singleton_iff.mp hx; exact hX'int)
  have hY'int : _root_.IsIntegral F (W.addYFun a b) :=
    isIntegral_trans (W.addYFun a b) (isIntegral_addYFun_adjoin_addXFun hA)
  have hKalg : Algebra.IsAlgebraic F
      (IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)) :=
    IntermediateField.isAlgebraic_adjoin (fun x hx => by
      rcases hx with rfl | rfl
      · exact hX'int
      · exact hY'int)
  have hXmem : polyToFunctionField W X
      ∈ IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField) :=
    polyToFunctionField_X_mem_adjoin_addFun hΔ hA
  have hXalg : IsAlgebraic F (polyToFunctionField W X) :=
    IntermediateField.isAlgebraic_iff.mp
      (Algebra.IsAlgebraic.isAlgebraic (⟨polyToFunctionField W X, hXmem⟩ :
        IntermediateField.adjoin F ({W.addXFun a b, W.addYFun a b} : Set W.FunctionField)))
  exact transcendental_polyToFunctionField_X hXalg

end Transcendence

section UnconditionalAut

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

def translationAlgEquivOf : W.FunctionField ≃ₐ[F] W.FunctionField :=
  translationAlgEquiv hA (addXFunTranscendental hΔ hA) hΔ

@[scoped simp] theorem translationAlgEquivOf_apply (z : W.FunctionField) :
    translationAlgEquivOf hΔ hA z = translationHom hA (addXFunTranscendental hΔ hA) z := rfl

@[scoped simp] theorem translationAlgEquivOf_polyToFunctionField_X :
    translationAlgEquivOf hΔ hA (polyToFunctionField W X) = W.addXFun a b :=
  translationHom_polyToFunctionField_X hA (addXFunTranscendental hΔ hA)

@[scoped simp] theorem translationAlgEquivOf_yGen :
    translationAlgEquivOf hΔ hA (yGen W) = W.addYFun a b :=
  translationHom_yGen hA (addXFunTranscendental hΔ hA)

end UnconditionalAut

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
section SubCarriers

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunKernelTranslationFixesAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (a b : F) (hab : W.toAffine.Equation a b),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), A.1 = a) →
          translationAlgEquivOf hΔ hab
              (W.toAffine.veluDeficitFun
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)))
            = W.toAffine.veluDeficitFun
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2))

def VeluDeficitFunKernelTranslationToInftyAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          ∃ (a b : F) (hab : W.toAffine.Equation a b),
            (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), A.1 = a) ∧
            ¬ IsFinitePlace (translationAlgEquivOf hΔ hab • v)

end SubCarriers

section Recombination

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunKernelTranslationAt_of_fixes_of_toInfty {p : ℕ}
    (hfix : VeluDeficitFunKernelTranslationFixesAt F p)
    (hto : VeluDeficitFunKernelTranslationToInftyAt F p) :
    VeluDeficitFunKernelTranslationAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv hk
  obtain ⟨a, b, hab, hka, hninf⟩ := hto W hΔ x₀ y₀ h₀ hord v hv hk
  exact ⟨translationAlgEquivOf hΔ hab, hfix W hΔ x₀ y₀ h₀ hord a b hab hka, hninf⟩

end Recombination

end WeierstrassCurve

end

section

noncomputable section

namespace WeierstrassCurve
section Helper

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma veluY_sub_self_eq_sum_singleton (S : Finset (F × F)) (r s : F) :
    W.veluY S r s - s = ∑ A ∈ S, (W.veluY {A} r s - s) := by
  simp only [veluY, Finset.sum_singleton, sub_sub_cancel_left, ← Finset.sum_neg_distrib]

end Helper

section BetaConstPoly

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
def veluYCorrConstNumPoly (A : F × F) : F[X] :=
  -(C (W.veluU A.1 A.2) * (C W.a₁ * X + C W.a₃))
    - (C (W.veluT A.1 A.2) * (C W.a₁ * (X - C A.1) - C A.2)
        + C (W.a₁ * W.veluU A.1 A.2 - W.veluGx A.1 A.2 * W.veluGy A.1 A.2)) * (X - C A.1)

omit [DecidableEq F] in
lemma veluYCorrConstNumPoly_natDegree_le (A : F × F) :
    (W.veluYCorrConstNumPoly A).natDegree ≤ 2 := by
  unfold veluYCorrConstNumPoly; compute_degree

def veluYCorrConstPadPoly (S : Finset (F × F)) (A : F × F) : F[X] :=
  W.veluYCorrConstNumPoly A * (∏ B ∈ S.erase A, (X - C B.1)) ^ 3

theorem eval_veluYCorrConstPadPoly {S : Finset (F × F)} {A : F × F} (hA : A ∈ S) {r : F}
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY {A} r 0 - 0) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r := by
  have hd : r - A.1 ≠ 0 := sub_ne_zero.mpr (hav A hA)
  have hsplit : (∏ B ∈ S, (r - B.1)) ^ 3
      = (r - A.1) ^ 3 * (∏ B ∈ S.erase A, (r - B.1)) ^ 3 := by
    rw [← mul_pow, ← Finset.prod_erase_mul S _ hA, mul_comm]
  rw [hsplit, veluYCorrConstPadPoly, veluYCorrConstNumPoly]
  simp only [veluY, Finset.sum_singleton, eval_mul, eval_neg, eval_add, eval_C, eval_sub, eval_X,
    eval_pow, eval_prod]
  field_simp
  ring

def veluYCorrConstSumPadPoly (S : Finset (F × F)) : F[X] := ∑ A ∈ S, W.veluYCorrConstPadPoly S A

theorem eval_veluYCorrConstSumPadPoly {S : Finset (F × F)} {r : F} (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY S r 0 - 0) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r := by
  rw [veluYCorrConstSumPadPoly, eval_finsetSum, W.veluY_sub_self_eq_sum_singleton, Finset.sum_mul]
  exact Finset.sum_congr rfl fun A hA => W.eval_veluYCorrConstPadPoly hA hav

end BetaConstPoly

section BetaSDecomp

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluY_sub_self_mul_prodCube_sDecomp {S : Finset (F × F)} {r : F} (s : F)
    (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY S r s - s) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r + (W.veluYCorrSCoeffSumPadPoly S).eval r * s := by
  have hlin := W.veluY_sub_self_sLinear S r s
  have hconst := W.eval_veluYCorrConstSumPadPoly (S := S) hav
  have hcoeff := W.veluY_sub_self_sCoeff_mul_prodPow_eq (S := S) hav
  have key : (W.veluY S r s - s)
      = (W.veluY S r 0 - 0) + (∑ A ∈ S, -(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * s := by
    linear_combination hlin
  rw [key, add_mul, hconst, mul_right_comm, hcoeff]

theorem veluY_singleton_sub_self_mul_prodCube_sDecomp {S : Finset (F × F)} {A : F × F}
    (hA : A ∈ S) {r : F} (s : F) (hav : ∀ B ∈ S, r ≠ B.1) :
    (W.veluY {A} r s - s) * (∏ B ∈ S, (r - B.1)) ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r + (W.veluYCorrSCoeffPadPoly S A).eval r * s := by
  have hlin := W.veluY_singleton_sub_sLinear A r s
  have hconst := W.eval_veluYCorrConstPadPoly hA hav
  have hcoeff := W.eval_veluYCorrSCoeffPadPoly hA (r := r) hav
  have key : (W.veluY {A} r s - s)
      = (W.veluY {A} r 0 - 0) + (-(2 * W.veluU A.1 A.2 / (r - A.1) ^ 3
          + W.veluT A.1 A.2 / (r - A.1) ^ 2)) * s := by
    linear_combination hlin
  rw [key, add_mul, hconst, mul_right_comm, hcoeff]

end BetaSDecomp

section TwoCrossTypes

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The square of the total Vélu `y`-correction minus the sum of the squares of the singleton
corrections. -/
@[expose] public def veluDeficitCrossQuadBetaSq (S : Finset (F × F)) (r s : F) : F :=
  (W.veluY S r s - s) ^ 2 - ∑ A ∈ S, (W.veluY {A} r s - s) ^ 2

/-- The product of the total Vélu coordinate corrections minus the sum of their singleton
products. -/
@[expose] public def veluDeficitCrossQuadAlphaBeta (S : Finset (F × F)) (r s : F) : F :=
  (W.veluX S r - r) * (W.veluY S r s - s)
    - ∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)

theorem veluDeficitCrossQuadBetaOnly_eq_betaSq_add_alphaBeta
    (S : Finset (F × F)) (r s : F) :
    W.veluDeficitCrossQuadBetaOnly S r s
      = W.veluDeficitCrossQuadBetaSq S r s + W.a₁ * W.veluDeficitCrossQuadAlphaBeta S r s := by
  classical
  rw [W.veluDeficitCrossQuadBetaOnly_eq, veluDeficitCrossQuadBetaSq,
    veluDeficitCrossQuadAlphaBeta]
  have hper : ∀ A ∈ S, ((W.veluY {A} r s - s) ^ 2
        + W.a₁ * (W.veluX {A} r - r) * (W.veluY {A} r s - s))
      = (W.veluY {A} r s - s) ^ 2
        + W.a₁ * ((W.veluX {A} r - r) * (W.veluY {A} r s - s)) := fun A _ => by ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end TwoCrossTypes

section Reduction

variable (F : Type*) [Field F] [DecidableEq F]

/-- The cleared squared-`y`-correction cross term is `M(x) + N(x)y`, with the degree of `M` below
four times the summing-set length. -/
@[expose] public def VeluDeficitCrossQuadBetaSqDecompDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M N : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadBetaSq
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r + N.eval r * s

/-- The cleared mixed-coordinate cross term is `M(x) + N(x)y`, with the degree of `M` below four
times the summing-set length. -/
@[expose] public def VeluDeficitCrossQuadAlphaBetaDecompDegLtAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 →
    ∀ (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∃ M N : F[X], M.natDegree < 4 * ((p - 1) / 2) ∧
          ∀ ⦃r s : F⦄, W.toAffine.Equation r s →
            (∀ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), r ≠ A.1) →
            W.veluDeficitCrossQuadAlphaBeta
                (W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)) r s
              * (∏ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
                    (r - A.1)) ^ 4
              = M.eval r + N.eval r * s

variable {F}

public theorem veluDeficitCrossQuadBetaSDecompDegLtAt_of_betaSq_of_alphaBeta
    {p : ℕ} (hBSq : VeluDeficitCrossQuadBetaSqDecompDegLtAt F p)
    (hαβ : VeluDeficitCrossQuadAlphaBetaDecompDegLtAt F p) :
    VeluDeficitCrossQuadBetaSDecompDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  obtain ⟨M₁, N₁, hM₁deg, hMN₁⟩ := hBSq W hΔ x₀ y₀ h₀ hord
  obtain ⟨M₂, N₂, hM₂deg, hMN₂⟩ := hαβ W hΔ x₀ y₀ h₀ hord
  refine ⟨M₁ + C W.a₁ * M₂, N₁ + C W.a₁ * N₂, ?_, ?_⟩
  · refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hM₁deg ?_)
    exact lt_of_le_of_lt (natDegree_mul_le.trans (by simp)) hM₂deg
  · intro r s hrs hav
    rw [W.veluDeficitCrossQuadBetaOnly_eq_betaSq_add_alphaBeta, add_mul, mul_assoc,
      hMN₁ hrs hav, hMN₂ hrs hav]
    simp only [eval_add, eval_mul, eval_C]; ring

end Reduction

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
universe u

variable {F : Type u} [Field F]

section CoordsAPI

variable {W : Affine F} (hΔ : W.Δ ≠ 0)

local notation "ι" => algebraMap F W.FunctionField

theorem genericPoint'_add_mapPoint_coordsOrZero {a b : F} (hA : W.Equation a b) :
    (Affine.genericPoint' hΔ + Affine.mapPoint hΔ hA).coordsOrZero
      = (W.addXFun a b, W.addYFun a b) := by
  rw [Affine.genericPoint'_add_map hΔ hA, Point.coordsOrZero_some]

end CoordsAPI

section AlgHomFixes

variable {K : Type*} [Field K] [Algebra F K]

theorem algHom_toRingHom_comp_algebraMap (τ : K →ₐ[F] K) :
    τ.toRingHom.comp (algebraMap F K) = algebraMap F K :=
  RingHom.ext fun c => τ.commutes c

theorem map_map_algHom_toRingHom_eq_self (W : WeierstrassCurve F) (τ : K →ₐ[F] K) :
    (W.map (algebraMap F K)).map τ.toRingHom = W.map (algebraMap F K) := by
  rw [WeierstrassCurve.map_map, algHom_toRingHom_comp_algebraMap]

variable (W : Affine F)

theorem liftSummingSet_map_algHom (τ : W.FunctionField →ₐ[F] W.FunctionField)
    (hτ : Function.Injective τ.toRingHom) (S : Finset (F × F)) :
    (W.liftSummingSet S).map ⟨Prod.map τ.toRingHom τ.toRingHom, hτ.prodMap hτ⟩
      = W.liftSummingSet S := by
  unfold liftSummingSet
  rw [Finset.map_map]
  congr 1
  refine Function.Embedding.ext fun ⟨c, d⟩ => ?_
  change (τ.toRingHom (algebraMap F W.FunctionField c), τ.toRingHom (algebraMap F W.FunctionField
    d)) = (algebraMap F W.FunctionField c, algebraMap F W.FunctionField d)
  rw [show τ.toRingHom (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c from
        τ.commutes c,
      show τ.toRingHom (algebraMap F W.FunctionField d) = algebraMap F W.FunctionField d from
        τ.commutes d]

end AlgHomFixes

section AlgHomNaturality

variable (W : Affine F)

local notation "ι" => algebraMap F W.FunctionField

theorem algHom_veluDeficit_liftSummingSet (τ : W.FunctionField →ₐ[F] W.FunctionField)
    (S : Finset (F × F)) (r s : W.FunctionField) :
    τ ((W.map ι).veluDeficit (W.liftSummingSet S) r s)
      = (W.map ι).veluDeficit (W.liftSummingSet S) (τ r) (τ s) := by
  have hτinj : Function.Injective τ.toRingHom := τ.toRingHom.injective
  have hkey := (W.map ι).map_veluDeficit τ.toRingHom (W.liftSummingSet S) hτinj r s
  rw [W.map_map_algHom_toRingHom_eq_self τ, W.liftSummingSet_map_algHom τ hτinj S] at hkey
  exact hkey.symm

theorem algHom_veluDeficitFun (τ : W.FunctionField →ₐ[F] W.FunctionField)
    (S : Finset (F × F)) :
    τ (W.veluDeficitFun S)
      = (W.map ι).veluDeficit (W.liftSummingSet S)
          (τ (polyToFunctionField W X)) (τ (yGen W)) :=
  W.algHom_veluDeficit_liftSummingSet τ S (polyToFunctionField W X) (yGen W)

end AlgHomNaturality

section TranslationAction

variable {W : Affine F} (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

theorem translationAlgEquivOf_veluDeficitFun (S : Finset (F × F)) :
    Affine.translationAlgEquivOf hΔ hA (W.veluDeficitFun S)
      = (W.map ι).veluDeficit (W.liftSummingSet S) (W.addXFun a b) (W.addYFun a b) := by
  rw [Affine.translationAlgEquivOf_apply,
    W.algHom_veluDeficitFun (Affine.translationHom hA (Affine.addXFunTranscendental hΔ hA)) S,
    Affine.translationHom_polyToFunctionField_X, Affine.translationHom_yGen]

theorem translationAlgEquivOf_veluDeficitFun_eq_coordsOrZero (S : Finset (F × F)) :
    Affine.translationAlgEquivOf hΔ hA (W.veluDeficitFun S)
      = (W.map ι).veluDeficit (W.liftSummingSet S)
          (Affine.genericPoint' hΔ + Affine.mapPoint hΔ hA).coordsOrZero.1
          (Affine.genericPoint' hΔ + Affine.mapPoint hΔ hA).coordsOrZero.2 := by
  rw [translationAlgEquivOf_veluDeficitFun hΔ hA S,
    genericPoint'_add_mapPoint_coordsOrZero hΔ hA]

theorem veluDeficitFun_eq_coordsOrZero_genericPoint' (S : Finset (F × F)) :
    W.veluDeficitFun S
      = (W.map ι).veluDeficit (W.liftSummingSet S)
          (Affine.genericPoint' hΔ).coordsOrZero.1
          (Affine.genericPoint' hΔ).coordsOrZero.2 :=
  rfl

theorem translationAlgEquivOf_veluDeficitFun_eq_iff (S : Finset (F × F)) :
    Affine.translationAlgEquivOf hΔ hA (W.veluDeficitFun S) = W.veluDeficitFun S
      ↔ (W.map ι).veluDeficit (W.liftSummingSet S)
            (Affine.genericPoint' hΔ + Affine.mapPoint hΔ hA).coordsOrZero.1
            (Affine.genericPoint' hΔ + Affine.mapPoint hΔ hA).coordsOrZero.2
          = (W.map ι).veluDeficit (W.liftSummingSet S)
            (Affine.genericPoint' hΔ).coordsOrZero.1
            (Affine.genericPoint' hΔ).coordsOrZero.2 := by
  rw [translationAlgEquivOf_veluDeficitFun_eq_coordsOrZero hΔ hA S,
    veluDeficitFun_eq_coordsOrZero_genericPoint' hΔ S]

end TranslationAction

section GenericNotConstant

variable {W : Affine F} (hΔ : W.Δ ≠ 0)

local notation "ι" => algebraMap F W.FunctionField

theorem genericPoint'_ne_some_algebraMap (c d : F)
    (hns : (W.map ι).Nonsingular (ι c) (ι d)) :
    Affine.genericPoint' hΔ ≠ Affine.Point.some (ι c) (ι d) hns := by
  intro h
  exact polyToFunctionField_X_ne_algebraMap c (Affine.Point.some.inj h).1

theorem genericPoint'_ne_zero : Affine.genericPoint' hΔ ≠ 0 :=
  Affine.Point.some_ne_zero _

end GenericNotConstant

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
namespace Affine

universe u

variable {F : Type u} [Field F] {W : Affine F}

section InverseOnX

variable (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

local notation "ι" => algebraMap F W.FunctionField

include hΔ hA in
theorem translationAlgEquivOf_addXFun_negY :
    translationAlgEquivOf hΔ hA (W.addXFun a (W.negY a b)) = polyToFunctionField W X := by
  classical
  have key := addFun_neg_cancel_X hΔ hA
  rw [Affine.slope_of_X_ne (addXFun_ne_algebraMap hΔ hA)] at key
  rw [addXFun, Affine.slope_of_X_ne (polyToFunctionField_X_ne_algebraMap a)]
  set τ := translationAlgEquivOf hΔ hA
  have hτX : τ (polyToFunctionField W X) = W.addXFun a b :=
    translationAlgEquivOf_polyToFunctionField_X hΔ hA
  have hτY : τ (yGen W) = W.addYFun a b := translationAlgEquivOf_yGen hΔ hA
  have hτι : ∀ c : F, τ (ι c) = ι c := fun c => τ.commutes c
  simp only [Affine.addX, map_a₁, map_a₂] at key ⊢
  simp only [map_sub, map_add, map_mul, map_pow, map_div₀, hτX, hτY, hτι]
  exact key

include hΔ hA in
theorem translationAlgEquivOf_symm_polyToFunctionField_X :
    (translationAlgEquivOf hΔ hA).symm (polyToFunctionField W X)
      = W.addXFun a (W.negY a b) :=
  (AlgEquiv.symm_apply_eq _).mpr (translationAlgEquivOf_addXFun_negY hΔ hA).symm

end InverseOnX

section Pole

variable [DecidableEq F]

local notation "ι" => algebraMap F W.FunctionField

omit [DecidableEq F] in
lemma algebraMap_XClass_eq (c : F) :
    algebraMap W.CoordinateRing W.FunctionField (XClass W c)
      = polyToFunctionField W X - ι c := by
  rw [show (XClass W c : W.CoordinateRing) = algebraMap F[X] W.CoordinateRing (X - C c) from rfl,
    ← polyToFunctionField_apply, map_sub, polyToFunctionField_C]

omit [DecidableEq F] in
lemma algebraMap_YClass_eq (c : F) :
    algebraMap W.CoordinateRing W.FunctionField (YClass W (C c)) = yGen W - ι c := by
  have h1 : (YClass W (C c) : W.CoordinateRing)
      = CoordinateRing.mk W Y - algebraMap F[X] W.CoordinateRing (C c) := by
    change CoordinateRing.mk W (Y - C (C c)) = _
    rw [map_sub]; rfl
  rw [h1, map_sub, ← polyToFunctionField_apply, polyToFunctionField_C]; rfl

omit [DecidableEq F] in
theorem addXFun_negY_notMem_of_XClass_mem_centre {a b : F}
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v)
    (hX : XClass W a ∈ hv.centre) (hY : YClass W (C (W.negY a b)) ∉ hv.centre) :
    W.addXFun a (W.negY a b) ∉ v.toValuationSubring := by
  set δX : W.FunctionField := polyToFunctionField W X - ι a with hδX
  set δY : W.FunctionField := yGen W - ι (W.negY a b) with hδY
  have hδX0 : δX ≠ 0 := X_sub_algebraMap_ne_zero a
  have hδY0 : δY ≠ 0 := hδY ▸ algebraMap_YClass_eq (W.negY a b) ▸
    algebraMap_coordinateRing_ne_zero (YClass_ne_zero (W' := W) (C (W.negY a b)))
  have hδXord : 1 ≤ v.ord δX := by
    have h1 : v.ord δX ≠ 0 := by
      have := (hv.mem_centre_iff_ord_ne_zero (XClass_ne_zero (W' := W) a)).mp hX
      rwa [algebraMap_XClass_eq] at this
    have h2 : 0 ≤ v.ord δX := by
      rw [hδX, ← algebraMap_XClass_eq]; exact v.ord_nonneg_of_mem (hv (XClass W a))
    omega
  have hδYord : v.ord δY = 0 := by
    have h1 : ¬ v.ord δY ≠ 0 := by
      rw [hδY, ← algebraMap_YClass_eq]
      exact fun hne => hY ((hv.mem_centre_iff_ord_ne_zero
        (YClass_ne_zero (W' := W) (C (W.negY a b)))).mpr hne)
    omega
  set ℓ : W.FunctionField := δY / δX with hℓ
  have hℓ0 : ℓ ≠ 0 := div_ne_zero hδY0 hδX0
  have hℓord : v.ord ℓ ≤ -1 := by rw [hℓ, v.ord_div hδY0 hδX0, hδYord]; omega
  have hℓnotmem : ℓ ∉ v.toValuationSubring := by
    rw [v.mem_iff_ord_nonneg hℓ0]; omega
  have hℓa₁notmem : ℓ + ι W.a₁ ∉ v.toValuationSubring := by
    intro hmem
    exact hℓnotmem (by simpa using sub_mem hmem (v.algebraMap_mem' W.a₁))
  have hprod_notmem : ℓ * (ℓ + ι W.a₁) ∉ v.toValuationSubring := by
    have hℓa₁0 : ℓ + ι W.a₁ ≠ 0 := by
      intro h0; exact hℓa₁notmem (h0 ▸ zero_mem v.toValuationSubring)
    rw [v.mem_iff_ord_nonneg (mul_ne_zero hℓ0 hℓa₁0), v.ord_mul hℓ0 hℓa₁0]
    have h1 : v.ord (ℓ + ι W.a₁) < 0 := by
      rw [← not_le, ← v.mem_iff_ord_nonneg hℓa₁0]; exact hℓa₁notmem
    omega
  have hkey : W.addXFun a (W.negY a b)
      = ℓ * (ℓ + ι W.a₁) - (ι W.a₂ + polyToFunctionField W X + ι a) := by
    rw [addXFun, Affine.slope_of_X_ne (polyToFunctionField_X_ne_algebraMap a)]
    simp only [Affine.addX, map_a₁, map_a₂, hℓ, hδX, hδY]
    ring
  intro hmem
  apply hprod_notmem
  have htail : (ι W.a₂ + polyToFunctionField W X + ι a : W.FunctionField)
      ∈ v.toValuationSubring :=
    add_mem (add_mem (v.algebraMap_mem' W.a₂)
      (polyToFunctionField_apply (W := W) X ▸ hv (algebraMap F[X] W.CoordinateRing X)))
      (v.algebraMap_mem' a)
  have := add_mem hmem htail
  rwa [hkey, sub_add_cancel] at this

end Pole

section CombinedDischarge

variable (hΔ : W.Δ ≠ 0) {a b : F} (hA : W.Equation a b)

theorem not_isFinitePlace_translationAlgEquivOf_smul_of_centre
    {v : AlgebraicCurve.Place F W.FunctionField} (hv : IsFinitePlace v)
    (hX : XClass W a ∈ hv.centre) (hY : YClass W (C (W.negY a b)) ∉ hv.centre) :
    ¬ IsFinitePlace (translationAlgEquivOf hΔ hA • v) := by
  apply not_isFinitePlace_smul_of_symm_X_notMem (translationAlgEquivOf hΔ hA) v
  rw [translationAlgEquivOf_symm_polyToFunctionField_X hΔ hA]
  exact addXFun_negY_notMem_of_XClass_mem_centre hv hX hY

end CombinedDischarge

end Affine
end WeierstrassCurve

namespace WeierstrassCurve
section YNotCentreCarrier

variable (F : Type*) [Field F] [DecidableEq F]

def VeluDeficitFunKernelTranslationYNotCentreAt (p : ℕ) : Prop :=
  ∀ (W : WeierstrassCurve F) (_ : W.Δ ≠ 0)
    (x₀ y₀ : F) (h₀ : W.toAffine.Nonsingular x₀ y₀),
      addOrderOf (Point.some x₀ y₀ h₀ : W.toAffine.Point) = p →
        ∀ (v : Place F W.toAffine.FunctionField) (hv : IsFinitePlace v),
          (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2),
            XClass W.toAffine A.1 ∈ hv.centre) →
          ∃ (a b : F) (_ : W.toAffine.Equation a b),
            (∃ A ∈ W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2), A.1 = a) ∧
            XClass W.toAffine a ∈ hv.centre ∧
            YClass W.toAffine (C (W.toAffine.negY a b)) ∉ hv.centre

end YNotCentreCarrier

section ToInftyFromYNotCentre

variable (F : Type*) [Field F] [DecidableEq F]

theorem veluDeficitFunKernelTranslationToInftyAt_of_yNotCentre {p : ℕ}
    (hY : VeluDeficitFunKernelTranslationYNotCentreAt F p) :
    VeluDeficitFunKernelTranslationToInftyAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv hk
  obtain ⟨a, b, hab, hka, hXcen, hYcen⟩ := hY W hΔ x₀ y₀ h₀ hord v hv hk
  exact ⟨a, b, hab, hka,
    Affine.not_isFinitePlace_translationAlgEquivOf_smul_of_centre hΔ hab hv hXcen hYcen⟩

end ToInftyFromYNotCentre

end WeierstrassCurve

end

section

noncomputable section

namespace WeierstrassCurve
section Helper

lemma prod_sum_sub_sum_diag_eq {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → R) :
    (∑ A ∈ s, f A) * (∑ B ∈ s, g B) - ∑ A ∈ s, f A * g A
      = ∑ A ∈ s, ∑ B ∈ s.erase A, f A * g B := by
  have key : ∀ A ∈ s, f A * (∑ B ∈ s, g B)
      = f A * g A + ∑ B ∈ s.erase A, f A * g B := by
    intro A hA
    rw [← Finset.mul_sum, ← Finset.add_sum_erase s g hA, mul_add]
  rw [Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_add_distrib, add_sub_cancel_left]

end Helper

section MixedPairPad

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluXYCorrConstPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluXCorrNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) ^ 2 * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

def veluXYCorrSCoeffPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluXCorrNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) ^ 2 * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

theorem veluXCorrPadPoly_mul_veluYCorrConstPadPoly_eq_kernelDenom_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluXCorrPadPoly S A * W.veluYCorrConstPadPoly S B
      = veluKernelDenom S * W.veluXYCorrConstPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluXCorrPadPoly veluYCorrConstPadPoly veluXYCorrConstPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluXCorrPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluXCorrPadPoly S A * W.veluYCorrSCoeffPadPoly S B
      = veluKernelDenom S * W.veluXYCorrSCoeffPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluXCorrPadPoly veluYCorrSCoeffPadPoly veluXYCorrSCoeffPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

end MixedPairPad

section AlphaBetaCleared

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadAlphaBetaConstClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluXYCorrConstPairPadQuot S A B

def veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluXYCorrSCoeffPairPadQuot S A B

theorem veluXCorrSumPadPoly_mul_veluYCorrConstSumPadPoly_sub_sum_eq (S : Finset (F × F)) :
    W.veluXCorrSumPadPoly S * W.veluYCorrConstSumPadPoly S
        - ∑ A ∈ S, W.veluXCorrPadPoly S A * W.veluYCorrConstPadPoly S A
      = veluKernelDenom S * W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S := by
  rw [veluXCorrSumPadPoly, veluYCorrConstSumPadPoly,
    prod_sum_sub_sum_diag_eq S _ _, veluDeficitCrossQuadAlphaBetaConstClearedPoly,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluXCorrPadPoly_mul_veluYCorrConstPadPoly_eq_kernelDenom_mul hA hBS hBA.symm

theorem veluXCorrSumPadPoly_mul_veluYCorrSCoeffSumPadPoly_sub_sum_eq (S : Finset (F × F)) :
    W.veluXCorrSumPadPoly S * W.veluYCorrSCoeffSumPadPoly S
        - ∑ A ∈ S, W.veluXCorrPadPoly S A * W.veluYCorrSCoeffPadPoly S A
      = veluKernelDenom S * W.veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly S := by
  rw [veluXCorrSumPadPoly, veluYCorrSCoeffSumPadPoly,
    prod_sum_sub_sum_diag_eq S _ _, veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluXCorrPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_mul hA hBS hBA.symm

theorem veluDeficitCrossQuadAlphaBeta_mul_prodPow_sDecomp {S : Finset (F × F)} {r : F} (s : F)
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadAlphaBeta S r s * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S).eval r
        + (W.veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly S).eval r * s := by
  set D : F := ∏ B ∈ S, (r - B.1) with hD_def
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun B hB => sub_ne_zero.mpr (hav B hB)
  have hαS : (W.veluX S r - r) * D ^ 2 = (W.veluXCorrSumPadPoly S).eval r :=
    hD_def ▸ W.eval_veluXCorrSumPadPoly hav
  have hβS : (W.veluY S r s - s) * D ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r + (W.veluYCorrSCoeffSumPadPoly S).eval r * s :=
    hD_def ▸ W.veluY_sub_self_mul_prodCube_sDecomp s hav
  have hαA : ∀ A ∈ S, (W.veluX {A} r - r) * D ^ 2 = (W.veluXCorrPadPoly S A).eval r :=
    fun A hA => hD_def ▸ W.eval_veluXCorrPadPoly hA hav
  have hβA : ∀ A ∈ S, (W.veluY {A} r s - s) * D ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r + (W.veluYCorrSCoeffPadPoly S A).eval r * s :=
    fun A hA => hD_def ▸ W.veluY_singleton_sub_self_mul_prodCube_sDecomp hA s hav
  refine mul_left_cancel₀ hD ?_
  have hLHS : D * (W.veluDeficitCrossQuadAlphaBeta S r s * D ^ 4)
      = ((W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrConstSumPadPoly S).eval r
            - ∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r * (W.veluYCorrConstPadPoly S A).eval r)
        + ((W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrSCoeffSumPadPoly S).eval r
            - ∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r
                * (W.veluYCorrSCoeffPadPoly S A).eval r) * s := by
    have htop : ((W.veluX S r - r) * (W.veluY S r s - s)) * (D ^ 2 * D ^ 3)
        = (W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrConstSumPadPoly S).eval r
          + ((W.veluXCorrSumPadPoly S).eval r * (W.veluYCorrSCoeffSumPadPoly S).eval r) * s := by
      rw [show (W.veluX S r - r) * (W.veluY S r s - s) * (D ^ 2 * D ^ 3)
          = ((W.veluX S r - r) * D ^ 2) * ((W.veluY S r s - s) * D ^ 3) from by ring,
        hαS, hβS]; ring
    have hsum : (∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)) * (D ^ 2 * D ^ 3)
        = (∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r * (W.veluYCorrConstPadPoly S A).eval r)
          + (∑ A ∈ S, (W.veluXCorrPadPoly S A).eval r
              * (W.veluYCorrSCoeffPadPoly S A).eval r) * s := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun A hA => ?_
      rw [show (W.veluX {A} r - r) * (W.veluY {A} r s - s) * (D ^ 2 * D ^ 3)
          = ((W.veluX {A} r - r) * D ^ 2) * ((W.veluY {A} r s - s) * D ^ 3) from by ring,
        hαA A hA, hβA A hA]; ring
    unfold veluDeficitCrossQuadAlphaBeta
    rw [show D * (((W.veluX S r - r) * (W.veluY S r s - s)
            - ∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)) * D ^ 4)
        = ((W.veluX S r - r) * (W.veluY S r s - s)) * (D ^ 2 * D ^ 3)
          - (∑ A ∈ S, (W.veluX {A} r - r) * (W.veluY {A} r s - s)) * (D ^ 2 * D ^ 3) from by ring,
      htop, hsum]; ring
  rw [hLHS]
  have hM := congrArg (Polynomial.eval r)
    (W.veluXCorrSumPadPoly_mul_veluYCorrConstSumPadPoly_sub_sum_eq S)
  have hN := congrArg (Polynomial.eval r)
    (W.veluXCorrSumPadPoly_mul_veluYCorrSCoeffSumPadPoly_sub_sum_eq S)
  simp only [eval_sub, eval_mul, eval_finsetSum, eval_veluKernelDenom, ← hD_def] at hM hN
  rw [hM, hN]; ring

end AlphaBetaCleared

section DegBound

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluXYCorrConstPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluXYCorrConstPairPadQuot S A B).natDegree ≤ 4 * S.card - 2 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hScard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
  unfold veluXYCorrConstPairPadQuot
  calc (W.veluXCorrNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) ^ 2 * (X - C B.1)
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 4).natDegree
      ≤ ((1 + 2) + 2 + 1) + 4 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          refine natDegree_mul_le.trans (add_le_add ?_ ?_)
          · exact natDegree_mul_le.trans (add_le_add (W.veluXCorrNumPoly_natDegree_le A)
              (W.veluYCorrConstNumPoly_natDegree_le B))
          · simp [natDegree_pow]
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 4 * S.card - 2 := by omega

theorem veluDeficitCrossQuadAlphaBetaConstClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1)
    (natDegree_le_iff_degree_le.mpr ?_) (by omega)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_)
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  refine degree_le_natDegree.trans (Nat.cast_le.mpr ?_)
  exact (W.veluXYCorrConstPairPadQuot_natDegree_le hA hBS hBA.symm).trans (by omega)

end DegBound

end WeierstrassCurve

end

section

noncomputable section

namespace WeierstrassCurve
section Helper

lemma sq_sum_sub_sum_sq_eq {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → R) :
    (∑ A ∈ s, f A) ^ 2 - ∑ A ∈ s, f A ^ 2
      = ∑ A ∈ s, ∑ B ∈ s.erase A, f A * f B := by
  have key : ∀ A ∈ s, f A * (∑ B ∈ s, f B)
      = f A ^ 2 + ∑ B ∈ s.erase A, f A * f B := by
    intro A hA
    rw [← Finset.mul_sum, ← Finset.add_sum_erase s f hA, mul_add, sq]
  rw [sq, Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_add_distrib, add_sub_cancel_left]

lemma prod_sum_sub_sum_diag_eq' {R : Type*} [CommRing R] {α : Type*} [DecidableEq α]
    (s : Finset α) (f g : α → R) :
    (∑ A ∈ s, f A) * (∑ B ∈ s, g B) - ∑ A ∈ s, f A * g A
      = ∑ A ∈ s, ∑ B ∈ s.erase A, f A * g B := by
  have key : ∀ A ∈ s, f A * (∑ B ∈ s, g B)
      = f A * g A + ∑ B ∈ s.erase A, f A * g B := by
    intro A hA
    rw [← Finset.mul_sum, ← Finset.add_sum_erase s g hA, mul_add]
  rw [Finset.sum_mul, Finset.sum_congr rfl key, Finset.sum_add_distrib, add_sub_cancel_left]

end Helper

section BetaSqPairPad

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluYYCorrConstPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluYCorrConstNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

def veluYYCorrCrossPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluYCorrConstNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

def veluYYCorrSCoeffPairPadQuot (S : Finset (F × F)) (A B : F × F) : F[X] :=
  W.veluYCorrSCoeffNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) * (X - C B.1)
    * (∏ E ∈ (S.erase A).erase B, (X - C E.1)) ^ 4

theorem veluYCorrConstPadPoly_mul_eq_kernelDenom_sq_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluYCorrConstPadPoly S A * W.veluYCorrConstPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluYYCorrConstPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluYCorrConstPadPoly veluYYCorrConstPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluYCorrConstPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_sq_mul
    {S : Finset (F × F)} {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluYCorrConstPadPoly S A * W.veluYCorrSCoeffPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluYYCorrCrossPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluYCorrConstPadPoly veluYCorrSCoeffPadPoly veluYYCorrCrossPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

theorem veluYCorrSCoeffPadPoly_mul_eq_kernelDenom_sq_mul {S : Finset (F × F)}
    {A B : F × F} (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    W.veluYCorrSCoeffPadPoly S A * W.veluYCorrSCoeffPadPoly S B
      = (veluKernelDenom S) ^ 2 * W.veluYYCorrSCoeffPairPadQuot S A B := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hAB' : A ∈ S.erase B := Finset.mem_erase.mpr ⟨hAB, hA⟩
  unfold veluYCorrSCoeffPadPoly veluYYCorrSCoeffPairPadQuot veluKernelDenom
  rw [← Finset.mul_prod_erase (S.erase A) _ hBA,
      ← Finset.mul_prod_erase (S.erase B) _ hAB',
      Finset.erase_right_comm (a := B),
      ← Finset.mul_prod_erase S _ hA,
      ← Finset.mul_prod_erase (S.erase A) _ hBA]
  ring

end BetaSqPairPad

section BetaSqCleared

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def veluDeficitCrossQuadBetaSqConstClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluYYCorrConstPairPadQuot S A B

def veluDeficitCrossQuadBetaSqCrossClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluYYCorrCrossPairPadQuot S A B

def veluDeficitCrossQuadBetaSqSqClearedPoly (S : Finset (F × F)) : F[X] :=
  ∑ A ∈ S, ∑ B ∈ S.erase A, W.veluYYCorrSCoeffPairPadQuot S A B

theorem veluYCorrConstSumPadPoly_sq_sub_sum_sq_eq (S : Finset (F × F)) :
    (W.veluYCorrConstSumPadPoly S) ^ 2 - ∑ A ∈ S, (W.veluYCorrConstPadPoly S A) ^ 2
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadBetaSqConstClearedPoly S := by
  rw [veluYCorrConstSumPadPoly, veluDeficitCrossQuadBetaSqConstClearedPoly,
    sq_sum_sub_sum_sq_eq S _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluYCorrConstPadPoly_mul_eq_kernelDenom_sq_mul hA hBS hBA.symm

theorem veluYCorrConstSumPadPoly_mul_SCoeffSumPadPoly_sub_sum_eq (S : Finset (F × F)) :
    W.veluYCorrConstSumPadPoly S * W.veluYCorrSCoeffSumPadPoly S
        - ∑ A ∈ S, W.veluYCorrConstPadPoly S A * W.veluYCorrSCoeffPadPoly S A
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadBetaSqCrossClearedPoly S := by
  rw [veluYCorrConstSumPadPoly, veluYCorrSCoeffSumPadPoly,
    veluDeficitCrossQuadBetaSqCrossClearedPoly, prod_sum_sub_sum_diag_eq' S _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluYCorrConstPadPoly_mul_veluYCorrSCoeffPadPoly_eq_kernelDenom_sq_mul hA hBS hBA.symm

theorem veluYCorrSCoeffSumPadPoly_sq_sub_sum_sq_eq (S : Finset (F × F)) :
    (W.veluYCorrSCoeffSumPadPoly S) ^ 2 - ∑ A ∈ S, (W.veluYCorrSCoeffPadPoly S A) ^ 2
      = (veluKernelDenom S) ^ 2 * W.veluDeficitCrossQuadBetaSqSqClearedPoly S := by
  rw [veluYCorrSCoeffSumPadPoly, veluDeficitCrossQuadBetaSqSqClearedPoly,
    sq_sum_sub_sum_sq_eq S _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact W.veluYCorrSCoeffPadPoly_mul_eq_kernelDenom_sq_mul hA hBS hBA.symm

theorem veluDeficitCrossQuadBetaSq_mul_prodPow_sQuadDecomp {S : Finset (F × F)} {r : F} (s : F)
    (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadBetaSq S r s * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadBetaSqConstClearedPoly S).eval r
        + 2 * (W.veluDeficitCrossQuadBetaSqCrossClearedPoly S).eval r * s
        + (W.veluDeficitCrossQuadBetaSqSqClearedPoly S).eval r * s ^ 2 := by
  set D : F := ∏ B ∈ S, (r - B.1) with hD_def
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun B hB => sub_ne_zero.mpr (hav B hB)
  have hβS : (W.veluY S r s - s) * D ^ 3
      = (W.veluYCorrConstSumPadPoly S).eval r + (W.veluYCorrSCoeffSumPadPoly S).eval r * s :=
    hD_def ▸ W.veluY_sub_self_mul_prodCube_sDecomp s hav
  have hβA : ∀ A ∈ S, (W.veluY {A} r s - s) * D ^ 3
      = (W.veluYCorrConstPadPoly S A).eval r + (W.veluYCorrSCoeffPadPoly S A).eval r * s :=
    fun A hA => hD_def ▸ W.veluY_singleton_sub_self_mul_prodCube_sDecomp hA s hav
  refine mul_left_cancel₀ (pow_ne_zero 2 hD) ?_
  have hLHS : D ^ 2 * (W.veluDeficitCrossQuadBetaSq S r s * D ^ 4)
      = ((W.veluYCorrConstSumPadPoly S).eval r ^ 2
            - ∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r ^ 2)
        + 2 * ((W.veluYCorrConstSumPadPoly S).eval r * (W.veluYCorrSCoeffSumPadPoly S).eval r
            - ∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r
                * (W.veluYCorrSCoeffPadPoly S A).eval r) * s
        + ((W.veluYCorrSCoeffSumPadPoly S).eval r ^ 2
            - ∑ A ∈ S, (W.veluYCorrSCoeffPadPoly S A).eval r ^ 2) * s ^ 2 := by
    have htop : ((W.veluY S r s - s) * D ^ 3) ^ 2
        = (W.veluYCorrConstSumPadPoly S).eval r ^ 2
          + 2 * ((W.veluYCorrConstSumPadPoly S).eval r
              * (W.veluYCorrSCoeffSumPadPoly S).eval r) * s
          + (W.veluYCorrSCoeffSumPadPoly S).eval r ^ 2 * s ^ 2 := by
      rw [hβS]; ring
    have hsum : ∑ A ∈ S, ((W.veluY {A} r s - s) * D ^ 3) ^ 2
        = (∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r ^ 2)
          + 2 * (∑ A ∈ S, (W.veluYCorrConstPadPoly S A).eval r
              * (W.veluYCorrSCoeffPadPoly S A).eval r) * s
          + (∑ A ∈ S, (W.veluYCorrSCoeffPadPoly S A).eval r ^ 2) * s ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun A hA => by rw [hβA A hA]; ring
    unfold veluDeficitCrossQuadBetaSq
    have hreorg : D ^ 2 * (((W.veluY S r s - s) ^ 2
            - ∑ A ∈ S, (W.veluY {A} r s - s) ^ 2) * D ^ 4)
        = ((W.veluY S r s - s) * D ^ 3) ^ 2
          - ∑ A ∈ S, ((W.veluY {A} r s - s) * D ^ 3) ^ 2 := by
      simp only [mul_pow, ← Finset.sum_mul]; ring
    rw [hreorg, htop, hsum]; ring
  rw [hLHS]
  have hM00 := congrArg (Polynomial.eval r) (W.veluYCorrConstSumPadPoly_sq_sub_sum_sq_eq S)
  have hM01 := congrArg (Polynomial.eval r)
    (W.veluYCorrConstSumPadPoly_mul_SCoeffSumPadPoly_sub_sum_eq S)
  have hM11 := congrArg (Polynomial.eval r) (W.veluYCorrSCoeffSumPadPoly_sq_sub_sum_sq_eq S)
  simp only [eval_sub, eval_mul, eval_pow, eval_finsetSum, eval_veluKernelDenom,
    ← hD_def] at hM00 hM01 hM11
  rw [hM00, hM01, hM11]; ring

end BetaSqCleared

section S2Reduction

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
def veluWeierstrassCubicPoly : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

omit [DecidableEq F] in
lemma veluWeierstrassCubicPoly_natDegree_le : W.veluWeierstrassCubicPoly.natDegree ≤ 3 := by
  unfold veluWeierstrassCubicPoly; compute_degree

omit [DecidableEq F] in
theorem sq_eq_veluWeierstrassCubicPoly_sub_of_equation {r s : F} (hrs : W.toAffine.Equation r s) :
    s ^ 2 = W.veluWeierstrassCubicPoly.eval r - (W.a₁ * r + W.a₃) * s := by
  have heq := (Affine.equation_iff r s).mp hrs
  simp only [veluWeierstrassCubicPoly, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination heq

def veluDeficitCrossQuadBetaSqConstS2ClearedPoly (S : Finset (F × F)) : F[X] :=
  W.veluDeficitCrossQuadBetaSqConstClearedPoly S
    + W.veluWeierstrassCubicPoly * W.veluDeficitCrossQuadBetaSqSqClearedPoly S

def veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly (S : Finset (F × F)) : F[X] :=
  2 * W.veluDeficitCrossQuadBetaSqCrossClearedPoly S
    - (C W.a₁ * X + C W.a₃) * W.veluDeficitCrossQuadBetaSqSqClearedPoly S

theorem veluDeficitCrossQuadBetaSq_mul_prodPow_sDecomp {S : Finset (F × F)} {r s : F}
    (hrs : W.toAffine.Equation r s) (hav : ∀ B ∈ S, r ≠ B.1) :
    W.veluDeficitCrossQuadBetaSq S r s * (∏ B ∈ S, (r - B.1)) ^ 4
      = (W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S).eval r
        + (W.veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly S).eval r * s := by
  rw [W.veluDeficitCrossQuadBetaSq_mul_prodPow_sQuadDecomp s hav,
    W.sq_eq_veluWeierstrassCubicPoly_sub_of_equation hrs,
    veluDeficitCrossQuadBetaSqConstS2ClearedPoly, veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly]
  simp only [eval_add, eval_mul, eval_sub, eval_ofNat, eval_C, eval_X]
  ring

end S2Reduction

section DegBound

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem veluYYCorrConstPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluYYCorrConstPairPadQuot S A B).natDegree ≤ 4 * S.card - 2 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hScard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
  unfold veluYYCorrConstPairPadQuot
  calc (W.veluYCorrConstNumPoly A * W.veluYCorrConstNumPoly B * (X - C A.1) * (X - C B.1)
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 4).natDegree
      ≤ ((2 + 2) + 1 + 1) + 4 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          exact natDegree_mul_le.trans (add_le_add (W.veluYCorrConstNumPoly_natDegree_le A)
            (W.veluYCorrConstNumPoly_natDegree_le B))
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 4 * S.card - 2 := by omega

theorem veluYYCorrSCoeffPairPadQuot_natDegree_le {S : Finset (F × F)} {A B : F × F}
    (hA : A ∈ S) (hB : B ∈ S) (hAB : A ≠ B) :
    (W.veluYYCorrSCoeffPairPadQuot S A B).natDegree ≤ 4 * S.card - 4 := by
  have hBA : B ∈ S.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hScard : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨A, hA, B, hB, hAB⟩
  unfold veluYYCorrSCoeffPairPadQuot
  calc (W.veluYCorrSCoeffNumPoly A * W.veluYCorrSCoeffNumPoly B * (X - C A.1) * (X - C B.1)
          * (∏ E ∈ (S.erase A).erase B, ((X : F[X]) - C E.1)) ^ 4).natDegree
      ≤ ((1 + 1) + 1 + 1) + 4 * (S.card - 2) := by
        refine natDegree_mul_le.trans (add_le_add ?_ ?_)
        · refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          refine natDegree_mul_le.trans (add_le_add ?_ (natDegree_X_sub_C _).le)
          exact natDegree_mul_le.trans (add_le_add (W.veluYCorrSCoeffNumPoly_natDegree_le A)
            (W.veluYCorrSCoeffNumPoly_natDegree_le B))
        · rw [natDegree_pow, natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
          simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.card_erase_of_mem hBA, Finset.card_erase_of_mem hA]
          omega
    _ ≤ 4 * S.card - 4 := by omega

theorem veluDeficitCrossQuadBetaSqConstClearedPoly_natDegree_le (S : Finset (F × F)) :
    (W.veluDeficitCrossQuadBetaSqConstClearedPoly S).natDegree ≤ 4 * S.card - 2 := by
  refine natDegree_le_iff_degree_le.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact degree_le_natDegree.trans
    (Nat.cast_le.mpr (W.veluYYCorrConstPairPadQuot_natDegree_le hA hBS hBA.symm))

theorem veluDeficitCrossQuadBetaSqSqClearedPoly_natDegree_le (S : Finset (F × F)) :
    (W.veluDeficitCrossQuadBetaSqSqClearedPoly S).natDegree ≤ 4 * S.card - 4 := by
  refine natDegree_le_iff_degree_le.mpr ((degree_sum_le _ _).trans (Finset.sup_le fun A hA => ?_))
  refine ((degree_sum_le _ _).trans (Finset.sup_le fun B hB => ?_))
  obtain ⟨hBA, hBS⟩ := Finset.mem_erase.mp hB
  exact degree_le_natDegree.trans
    (Nat.cast_le.mpr (W.veluYYCorrSCoeffPairPadQuot_natDegree_le hA hBS hBA.symm))

theorem veluDeficitCrossQuadBetaSqConstS2ClearedPoly_natDegree_lt {S : Finset (F × F)}
    (hS : S.Nonempty) :
    (W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S).natDegree < 4 * S.card := by
  have hScard : 0 < S.card := Finset.card_pos.mpr hS
  refine lt_of_le_of_lt (b := 4 * S.card - 1) ?_ (by omega)
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (W.veluDeficitCrossQuadBetaSqConstClearedPoly_natDegree_le S).trans (by omega)
  · refine natDegree_mul_le.trans ?_
    have h₁ := W.veluWeierstrassCubicPoly_natDegree_le
    have h₂ := W.veluDeficitCrossQuadBetaSqSqClearedPoly_natDegree_le S
    omega

end DegBound

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
universe u

variable {F : Type u} [Field F]

section CoordsAPI

variable {k : Type*} [Field k] (f : F →+* k) {W : WeierstrassCurve F}

theorem coordsOrZero_ratPointMap (P : W.toAffine.Point) :
    (ratPointMap f P).coordsOrZero = (f P.coordsOrZero.1, f P.coordsOrZero.2) := by
  rcases P with _ | ⟨x, y, h⟩
  · change ((0, 0) : k × k) = (f 0, f 0); rw [_root_.map_zero]
  · rfl

end CoordsAPI

section SummingSetCompat

variable [DecidableEq F] (W : Affine F)

local notation "ι" => algebraMap F W.FunctionField

variable [DecidableEq W.FunctionField]

theorem liftSummingSet_oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) :
    W.liftSummingSet (W.oddOrderSummingSet Q n)
      = (W.map ι).oddOrderSummingSet (ratPointHom (W₀ := W) ι Q) n := by
  refine Finset.ext fun A => ?_
  simp only [liftSummingSet, oddOrderSummingSet, Finset.mem_map, Finset.mem_image,
    Finset.mem_Icc, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by
      rw [← map_nsmul, ratPointHom_apply, coordsOrZero_ratPointMap]; rfl⟩
  · rintro ⟨k, hk, hkA⟩
    exact ⟨(k • Q).coordsOrZero, ⟨k, hk, rfl⟩, by
      rw [← hkA, ← map_nsmul, ratPointHom_apply, coordsOrZero_ratPointMap]; rfl⟩

end SummingSetCompat

section GenericNotInRange

variable [DecidableEq F] {W : Affine F} (hΔ : W.Δ ≠ 0)

local notation "ι" => algebraMap F W.FunctionField

variable [DecidableEq W.FunctionField]

theorem genericPoint'_notMem_range_ratPointHom :
    Affine.genericPoint' hΔ ∉ (ratPointHom (W₀ := W) ι).range := by
  rintro ⟨P, hP⟩
  rcases P with _ | ⟨c, d, h⟩
  · exact genericPoint'_ne_zero hΔ hP.symm
  · exact genericPoint'_ne_some_algebraMap hΔ c d _ hP.symm

theorem genericPoint'_notMem_zmultiples_ratPointHom (Q : W.toAffine.Point) :
    Affine.genericPoint' hΔ ∉ AddSubgroup.zmultiples (ratPointHom (W₀ := W) ι Q) := by
  intro hmem
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  refine genericPoint'_notMem_range_ratPointHom hΔ ⟨n • Q, ?_⟩
  rw [map_zsmul, hn]

end GenericNotInRange

end WeierstrassCurve

end

noncomputable section

namespace WeierstrassCurve
lemma kw_vdcoog_some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    (Affine.Point.some x₁ y₁ h₁ : V.Point) = Affine.Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem kw_not_dvd_of_le_half_odd {p k : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) : ¬ p ∣ k ∧ ¬ p ∣ 2 * k := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  exact ⟨Nat.not_dvd_of_pos_of_lt (by omega) (by omega),
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)⟩

theorem kw_not_dvd_add_of_le_half_odd {p k k' : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2) :
    ¬ p ∣ k + k' := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by omega
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

section AbstractCofixed

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {p : ℕ}

theorem kw_exists_nsmul_of_mem_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) {P : F × F}
    (hP : P ∈ W.oddOrderSummingSet Q n) :
    ∃ (k : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y), 1 ≤ k ∧ k ≤ n ∧
      k • Q = Point.some x y h ∧ P = (x, y) ∧ (2 * k) • Q ≠ 0 := by
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  obtain ⟨hndvd, hndvd2⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk1 (hkn.trans hn)
  have hne : k • Q ≠ 0 := nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd
  obtain ⟨x, y, h, heq, hcoords⟩ := exists_some_of_ne_zero hne
  exact ⟨k, x, y, h, hk1, hkn, heq, by rw [← hkP, hcoords],
    nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd2⟩

theorem kw_nsmul_eq_of_xOrZero_eq_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {k k' : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2)
    (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2)
    {x y : F} {h : W.toAffine.Nonsingular x y} (heq : k • Q = Point.some x y h)
    {x' y' : F} {h' : W.toAffine.Nonsingular x' y'} (heq' : k' • Q = Point.some x' y' h')
    (hx : x = x') : k • Q = k' • Q := by
  rcases (Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hx with hPP | hPP
  · rw [heq, heq', hPP]
  · exfalso
    have hsum : (k + k') • Q = 0 := by rw [add_nsmul, heq, heq', hPP, _root_.neg_add_cancel]
    exact kw_not_dvd_add_of_le_half_odd hp3 hpodd hk1 hkn hk'1 hk'n
      (hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsum)

theorem kw_nsmul_injOn_odd (hp3 : 3 ≤ p) (hord : addOrderOf Q = p) {k k' : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ (p - 1) / 2) (hk'1 : 1 ≤ k') (hk'n : k' ≤ (p - 1) / 2)
    (heq : k • Q = k' • Q) : k = k' := by
  have hhalf : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  wlog hle : k ≤ k' generalizing k k'
  · exact (this hk'1 hk'n hk1 hkn heq.symm (by omega)).symm
  have hsub : (k' - k) • Q = 0 := by
    have : (k' - k) • Q + k • Q = k • Q := by
      rw [← add_nsmul, Nat.sub_add_cancel hle, heq]
    exact add_right_cancel (this.trans (zero_add _).symm)
  have hdvd : p ∣ k' - k := hord ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsub
  rcases Nat.eq_zero_or_pos (k' - k) with h0 | h0
  · omega
  · exact absurd hdvd (Nat.not_dvd_of_pos_of_lt h0 (by omega))

public theorem kw_isOddVeluSet_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    W.IsOddVeluSet (W.oddOrderSummingSet Q n) where
  equation P hP := by
    obtain ⟨_, _, _, h, _, _, _, hPxy, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP
    rw [hPxy]; exact h.left
  gy_ne_zero P hP := by
    obtain ⟨k, x, y, h, _, _, heq, hPxy, h2k⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP
    rw [hPxy]
    exact veluGy_ne_zero_of_two_nsmul_ne_zero h fun h2 => h2k (by
      rw [two_mul, add_nsmul, heq, ← two_nsmul, h2])
  x_injOn P hP P' hP' hx := by
    obtain ⟨k, x, y, h, hk1, hkn, heq, hPxy, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP
    obtain ⟨k', x', y', h', hk'1, hk'n, heq', hP'xy, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord hn hP'
    subst hPxy; subst hP'xy
    have hQQ' := kw_nsmul_eq_of_xOrZero_eq_odd hp3 hpodd hord hk1 (hkn.trans hn)
      hk'1 (hk'n.trans hn) heq heq' hx
    exact congrArg Point.coordsOrZero (heq ▸ heq' ▸ hQQ')

theorem kw_card_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    (W.oddOrderSummingSet Q n).card = n := by
  have hinj : Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 n : Finset ℕ) := by
    intro k hk k' hk' hcoords
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    obtain ⟨hndvd, _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk.1 (hk.2.trans hn)
    obtain ⟨hndvd', _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk'.1 (hk'.2.trans hn)
    obtain ⟨x, y, h, heq, hc⟩ :=
      exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd (k := k))
    obtain ⟨x', y', h', heq', hc'⟩ :=
      exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd' (k := k'))
    have hx : x = x' :=
      congrArg Prod.fst (show ((x, y) : F × F) = (x', y') from hc ▸ hc' ▸ hcoords)
    exact kw_nsmul_injOn_odd hp3 hord hk.1 (hk.2.trans hn) hk'.1 (hk'.2.trans hn)
      (kw_nsmul_eq_of_xOrZero_eq_odd hp3 hpodd hord hk.1 (hk.2.trans hn) hk'.1
        (hk'.2.trans hn) heq heq' hx)
  rw [oddOrderSummingSet, Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel]

end AbstractCofixed

section OrdNonneg

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
variable {Q : W.toAffine.Point} {p : ℕ}

theorem kw_veluX_oddOrderSummingSet_eq_sum_Icc_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) x
      = x + ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((Point.some x y hP + k • Q : W.toAffine.Point).xOrZero
            + (Point.some x y hP + -(k • Q) : W.toAffine.Point).xOrZero
            - 2 * (k • Q).xOrZero) := by
  set d := (p - 1) / 2
  have hSset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hx : ∀ A ∈ W.oddOrderSummingSet Q d, x ≠ A.1 := by
    intro A hA
    obtain ⟨k, a, b, h, _, _, heq, hAeq, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord le_rfl hA
    subst hAeq
    exact xOrZero_ne_of_not_mem_zmultiples hPmem
      (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
      (heq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  rw [W.veluX_eq_orbitSum hP.1 hSset.equation hx]
  congr 1
  have hcard := kw_card_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hIcc : (Finset.Icc 1 d).card = d := by rw [Nat.card_Icc]; omega
  have hinj : Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 d) := by
    rw [← Finset.card_image_iff]; exact hcard.trans hIcc.symm
  change ∑ A ∈ W.oddOrderSummingSet Q d, _ = _
  rw [oddOrderSummingSet, Finset.sum_image (fun a ha b hb => hinj ha hb)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  obtain ⟨hndvd, _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk.1 hk.2
  obtain ⟨a, b, hab, hkQeq, hkQc⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd)
  rw [hkQc]; dsimp only
  have hxk : x ≠ a := xOrZero_ne_of_not_mem_zmultiples hPmem
    (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
    (hkQeq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  have hPkQ : (Point.some x y hP + k • Q : W.toAffine.Point).xOrZero
      = W.toAffine.addX x a (W.toAffine.slope x a y b) := by
    rw [hkQeq, Point.add_of_X_ne hxk, Point.xOrZero_some]
  have hnegkQ : -(k • Q) =
      Point.some a (W.toAffine.negY a b) ((Affine.nonsingular_neg ..).mpr hab) := by
    rw [hkQeq]; rfl
  have hPmkQ : (Point.some x y hP + -(k • Q) : W.toAffine.Point).xOrZero
      = W.toAffine.addX x a (W.toAffine.slope x a y (W.toAffine.negY a b)) := by
    rw [hnegkQ, Point.add_of_X_ne hxk, Point.xOrZero_some]
  rw [hPkQ, hPmkQ, show (k • Q).xOrZero = a from by rw [hkQeq, Point.xOrZero_some]]

theorem kw_veluX_oddOrderSummingSet_eq_sum_range_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) x
      = (∑ j ∈ Finset.range p, (Point.some x y hP + j • Q : W.toAffine.Point).xOrZero)
        - 2 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k • Q).xOrZero := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  rw [kw_veluX_oddOrderSummingSet_eq_sum_Icc_odd hp3 hpodd hord hP hPmem]
  obtain ⟨d, hpeq, hd_def⟩ : ∃ d, p = 2 * d + 1 ∧ d = (p - 1) / 2 := ⟨(p - 1) / 2, by omega, rfl⟩
  rw [← hd_def, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    show ∀ a b c : F, a + (b - c) = a + b - c from fun a b c => (add_sub_assoc a b c).symm]
  congr 1
  have hsplit : Finset.range p = {0} ∪ Finset.Icc 1 d ∪ Finset.Icc (d + 1) (p - 1) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj1 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 d) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_singleton] at ha; rw [Finset.mem_Icc] at hb; omega
  have hdisj2 : Disjoint (({0} : Finset ℕ) ∪ Finset.Icc 1 d) (Finset.Icc (d + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at ha
    rw [Finset.mem_Icc] at hb; omega
  rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton,
    zero_nsmul, add_zero, Point.xOrZero_some]
  clear hd_def
  have hrefl : ∑ j ∈ Finset.Icc (d + 1) (p - 1),
        (Point.some x y hP + j • Q : W.toAffine.Point).xOrZero
      = ∑ k ∈ Finset.Icc 1 d,
        (Point.some x y hP + -(k • Q) : W.toAffine.Point).xOrZero := by
    refine Finset.sum_nbij' (fun j => p - j) (fun k => p - k)
      (fun j hj => by rw [Finset.mem_Icc] at hj; simp only [Finset.mem_Icc]; omega)
      (fun k hk => by rw [Finset.mem_Icc] at hk; simp only [Finset.mem_Icc]; omega)
      (fun j hj => by rw [Finset.mem_Icc] at hj; omega)
      (fun k hk => by rw [Finset.mem_Icc] at hk; omega)
      (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    congr 2
    have hpQ : p • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
    rw [← sub_nsmul_eq_neg_of_nsmul_eq_zero hpQ (k := p - j) (Nat.sub_le _ _)]
    congr 1; omega
  rw [hrefl]; ring

theorem kw_veluX_xOrZero_add_gen_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) :
    W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) (P + Q).xOrZero
      = W.veluX (W.oddOrderSummingSet Q ((p - 1) / 2)) P.xOrZero := by
  have hQmem : Q ∈ AddSubgroup.zmultiples Q := AddSubgroup.mem_zmultiples Q
  have hP0 : P ≠ 0 := fun h => hPmem (h ▸ AddSubgroup.zero_mem _)
  obtain ⟨x, y, hns, rfl, -⟩ := exists_some_of_ne_zero hP0
  have hPQmem := not_mem_zmultiples_add hPmem hQmem
  have hPQ0 : (Point.some x y hns + Q : W.toAffine.Point) ≠ 0 :=
    add_ne_zero_of_not_mem_zmultiples hPmem hQmem
  obtain ⟨x', y', hns', heqPQ, -⟩ := exists_some_of_ne_zero hPQ0
  rw [heqPQ, Point.xOrZero_some, Point.xOrZero_some,
    kw_veluX_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns' (heqPQ ▸ hPQmem),
    kw_veluX_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns hPmem]
  congr 1
  calc ∑ j ∈ Finset.range p, (Point.some x' y' hns' + j • Q : W.toAffine.Point).xOrZero
      = ∑ j ∈ Finset.range p,
          ((Point.some x y hns + Q : W.toAffine.Point) + j • Q).xOrZero :=
        Finset.sum_congr rfl fun j _ => by rw [← heqPQ]
    _ = ∑ j ∈ Finset.range p, (Point.some x y hns + j • Q : W.toAffine.Point).xOrZero :=
        sum_range_addOrderOf_shift_invariant hord _ _

theorem kw_veluY_oddOrderSummingSet_eq_sum_Icc_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) x y
      = y + ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((Point.some x y hP + k • Q : W.toAffine.Point).coordsOrZero.2
            + (Point.some x y hP + -(k • Q) : W.toAffine.Point).coordsOrZero.2
            - (k • Q).coordsOrZero.2
            - W.toAffine.negY (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) := by
  set d := (p - 1) / 2
  have hSset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hx : ∀ A ∈ W.oddOrderSummingSet Q d, x ≠ A.1 := by
    intro A hA
    obtain ⟨k, a, b, h, _, _, heq, hAeq, _⟩ :=
      kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord le_rfl hA
    subst hAeq
    exact xOrZero_ne_of_not_mem_zmultiples hPmem
      (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
      (heq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  rw [W.veluY_eq_orbitSum_fieldRed hP.1 hSset.equation hx]
  congr 1
  have hcard := kw_card_oddOrderSummingSet_odd (W := W) hp3 hpodd hord (le_refl d)
  have hIcc : (Finset.Icc 1 d).card = d := by rw [Nat.card_Icc]; omega
  have hinj : Set.InjOn (fun k : ℕ => (k • Q).coordsOrZero) (Finset.Icc 1 d) := by
    rw [← Finset.card_image_iff]; exact hcard.trans hIcc.symm
  change ∑ A ∈ W.oddOrderSummingSet Q d, _ = _
  rw [oddOrderSummingSet, Finset.sum_image (fun a ha b hb => hinj ha hb)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  obtain ⟨hndvd, _⟩ := kw_not_dvd_of_le_half_odd hp3 hpodd hk.1 hk.2
  obtain ⟨a, b, hab, hkQeq, hkQc⟩ :=
    exists_some_of_ne_zero (nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd hord hndvd)
  rw [hkQc]; dsimp only
  have hxk : x ≠ a := xOrZero_ne_of_not_mem_zmultiples hPmem
    (fun h0 => hPmem (h0 ▸ AddSubgroup.zero_mem _))
    (hkQeq ▸ AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) k)
  have hPkQ : (Point.some x y hP + k • Q : W.toAffine.Point).coordsOrZero.2
      = W.toAffine.addY x a y (W.toAffine.slope x a y b) := by
    rw [hkQeq, Point.add_of_X_ne hxk, Point.coordsOrZero_some]
  have hnegkQ : -(k • Q) = Point.some a (W.toAffine.negY a b)
      ((Affine.nonsingular_neg ..).mpr hab) := by
    rw [hkQeq]; rfl
  have hPmkQ : (Point.some x y hP + -(k • Q) : W.toAffine.Point).coordsOrZero.2
      = W.toAffine.addY x a y (W.toAffine.slope x a y (W.toAffine.negY a b)) := by
    rw [hnegkQ, Point.add_of_X_ne hxk, Point.coordsOrZero_some]
  rw [hPkQ, hPmkQ]

theorem kw_veluY_oddOrderSummingSet_eq_sum_range_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {x y : F} (hP : W.toAffine.Nonsingular x y)
    (hPmem : (Point.some x y hP : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q) :
    W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) x y
      = (∑ j ∈ Finset.range p,
          (Point.some x y hP + j • Q : W.toAffine.Point).coordsOrZero.2)
        - ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((k • Q).coordsOrZero.2
            + W.toAffine.negY (k • Q).coordsOrZero.1 (k • Q).coordsOrZero.2) := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  rw [kw_veluY_oddOrderSummingSet_eq_sum_Icc_odd hp3 hpodd hord hP hPmem]
  obtain ⟨d, hpeq, hd_def⟩ : ∃ d, p = 2 * d + 1 ∧ d = (p - 1) / 2 := ⟨(p - 1) / 2, by omega, rfl⟩
  rw [← hd_def]
  simp only [sub_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    show ∀ a b c : F, a + (b - c) = a + b - c from fun a b c => (add_sub_assoc a b c).symm]
  congr 1
  have hsplit : Finset.range p = {0} ∪ Finset.Icc 1 d ∪ Finset.Icc (d + 1) (p - 1) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hdisj1 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 d) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_singleton] at ha; rw [Finset.mem_Icc] at hb; omega
  have hdisj2 : Disjoint (({0} : Finset ℕ) ∪ Finset.Icc 1 d) (Finset.Icc (d + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at ha
    rw [Finset.mem_Icc] at hb; omega
  rw [hsplit, Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton,
    zero_nsmul, add_zero, Point.coordsOrZero_some]
  clear hd_def
  have hrefl : ∑ j ∈ Finset.Icc (d + 1) (p - 1),
        (Point.some x y hP + j • Q : W.toAffine.Point).coordsOrZero.2
      = ∑ k ∈ Finset.Icc 1 d,
        (Point.some x y hP + -(k • Q) : W.toAffine.Point).coordsOrZero.2 := by
    refine Finset.sum_nbij' (fun j => p - j) (fun k => p - k)
      (fun j hj => by rw [Finset.mem_Icc] at hj; simp only [Finset.mem_Icc]; omega)
      (fun k hk => by rw [Finset.mem_Icc] at hk; simp only [Finset.mem_Icc]; omega)
      (fun j hj => by rw [Finset.mem_Icc] at hj; omega)
      (fun k hk => by rw [Finset.mem_Icc] at hk; omega)
      (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    congr 3
    have hpQ : p • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
    rw [← sub_nsmul_eq_neg_of_nsmul_eq_zero hpQ (k := p - j) (Nat.sub_le _ _)]
    congr 1; omega
  rw [hrefl]; ring

theorem kw_veluY_coordsOrZero_add_gen_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {P : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) :
    W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) (P + Q).coordsOrZero.1
        (P + Q).coordsOrZero.2
      = W.veluY (W.oddOrderSummingSet Q ((p - 1) / 2)) P.coordsOrZero.1 P.coordsOrZero.2 := by
  have hQmem : Q ∈ AddSubgroup.zmultiples Q := AddSubgroup.mem_zmultiples Q
  have hP0 : P ≠ 0 := fun h => hPmem (h ▸ AddSubgroup.zero_mem _)
  obtain ⟨x, y, hns, rfl, -⟩ := exists_some_of_ne_zero hP0
  have hPQmem := not_mem_zmultiples_add hPmem hQmem
  have hPQ0 : (Point.some x y hns + Q : W.toAffine.Point) ≠ 0 :=
    add_ne_zero_of_not_mem_zmultiples hPmem hQmem
  obtain ⟨x', y', hns', heqPQ, -⟩ := exists_some_of_ne_zero hPQ0
  rw [heqPQ, Point.coordsOrZero_some, Point.coordsOrZero_some,
    kw_veluY_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns' (heqPQ ▸ hPQmem),
    kw_veluY_oddOrderSummingSet_eq_sum_range_odd hp3 hpodd hord hns hPmem]
  congr 1
  calc ∑ j ∈ Finset.range p, (Point.some x' y' hns' + j • Q : W.toAffine.Point).coordsOrZero.2
      = ∑ j ∈ Finset.range p,
          ((Point.some x y hns + Q : W.toAffine.Point) + j • Q).coordsOrZero.2 :=
        Finset.sum_congr rfl fun j _ => by rw [← heqPQ]
    _ = ∑ j ∈ Finset.range p, (Point.some x y hns + j • Q : W.toAffine.Point).coordsOrZero.2 :=
        sum_range_addOrderOf_shift_invariant hord
          (fun P => Point.coordsOrZero P |>.2) (Point.some x y hns)

theorem kw_veluDeficit_add_gen_odd (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)
    {P : W.toAffine.Point} (hPmem : P ∉ AddSubgroup.zmultiples Q) :
    W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        (P + Q).coordsOrZero.1 (P + Q).coordsOrZero.2
      = W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P.coordsOrZero.1 P.coordsOrZero.2 := by
  refine W.veluDeficit_congr ?_ (kw_veluY_coordsOrZero_add_gen_odd hp3 hpodd hord hPmem)
  rw [Point.coordsOrZero_fst, Point.coordsOrZero_fst]
  exact kw_veluX_xOrZero_add_gen_odd hp3 hpodd hord hPmem

theorem kw_veluDeficit_add_nsmul_odd (hp3 : 3 ≤ p) (hpodd : Odd p) (hord : addOrderOf Q = p)
    {P : W.toAffine.Point} (hPmem : P ∉ AddSubgroup.zmultiples Q) (n : ℕ) :
    W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        (P + n • Q).coordsOrZero.1 (P + n • Q).coordsOrZero.2
      = W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P.coordsOrZero.1 P.coordsOrZero.2 := by
  induction n with
  | zero => rw [zero_nsmul, add_zero]
  | succ m ih =>
    have hPm : P + m • Q ∉ AddSubgroup.zmultiples Q :=
      not_mem_zmultiples_add hPmem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples Q) m)
    rw [succ_nsmul, ← add_assoc, kw_veluDeficit_add_gen_odd hp3 hpodd hord hPm, ih]

theorem kw_veluDeficit_eq_of_sub_mem_zmultiples_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {P P' : W.toAffine.Point}
    (hPmem : P ∉ AddSubgroup.zmultiples Q) (hdiff : P' - P ∈ AddSubgroup.zmultiples Q) :
    W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P'.coordsOrZero.1 P'.coordsOrZero.2
      = W.veluDeficit (W.oddOrderSummingSet Q ((p - 1) / 2))
        P.coordsOrZero.1 P.coordsOrZero.2 := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hdiff
  have hpQ : (p : ℤ) • Q = 0 := by exact_mod_cast hord ▸ addOrderOf_nsmul_eq_zero Q
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  set n : ℕ := (k % (p : ℤ)).toNat with hn_def
  have hmod_nn := Int.emod_nonneg k hp_ne
  have hkQ : k • Q = n • Q := by
    conv_lhs => rw [show k = k % p + k / p * p from by
        rw [mul_comm]; exact (Int.emod_add_mul_ediv k p).symm,
      add_zsmul, mul_zsmul, hpQ, smul_zero, add_zero]
    rw [hn_def, ← natCast_zsmul, Int.toNat_of_nonneg hmod_nn]
  have hP'eq : P' = P + n • Q := by
    have h1 : P' - P = n • Q := hk ▸ hkQ
    rw [← h1, add_sub_cancel]
  rw [hP'eq]
  exact kw_veluDeficit_add_nsmul_odd hp3 hpodd hord hPmem n

theorem kw_mem_zmultiples_of_abscissa_mem_oddOrderSummingSet_odd (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hord : addOrderOf Q = p) {a b : F} (hab : W.toAffine.Nonsingular a b)
    (hA : ∃ A ∈ W.oddOrderSummingSet Q ((p - 1) / 2), A.1 = a) :
    Affine.Point.some a b hab ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨A, hAmem, hAfst⟩ := hA
  obtain ⟨k, xk, yk, hk, hk1, _, hkQ, hAeq, _⟩ :=
    kw_exists_nsmul_of_mem_oddOrderSummingSet_odd hp3 hpodd hord le_rfl hAmem
  have hax : a = xk := hAfst ▸ congrArg Prod.fst hAeq
  rcases Affine.Y_eq_of_X_eq hab.1 hk.1 hax with hby | hby
  · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨(k : ℤ), by
      rw [natCast_zsmul, hkQ]; exact kw_vdcoog_some_congr hax.symm hby.symm _ _⟩
  · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-(k : ℤ), by
      rw [neg_zsmul, natCast_zsmul, hkQ, Affine.Point.neg_some]
      exact kw_vdcoog_some_congr hax.symm hby.symm _ _⟩

variable (F : Type*) [Field F] [DecidableEq F] in
theorem kw_veluDeficitFunKernelTranslationFixesAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunKernelTranslationFixesAt F p := by
  intro W hΔ x₀ y₀ h₀ hord a b hab hA
  classical
  set ι := algebraMap F W.toAffine.FunctionField
  set Q : W.toAffine.Point := Affine.Point.some x₀ y₀ h₀
  set Q' : (W.map ι).toAffine.Point := ratPointHom (W₀ := W) ι Q
  rw [translationAlgEquivOf_veluDeficitFun_eq_iff hΔ hab,
    W.toAffine.liftSummingSet_oddOrderSummingSet Q ((p - 1) / 2)]
  have hord' : addOrderOf Q' = p :=
    (addOrderOf_injective (ratPointHom (W₀ := W) ι) (ratPointMap_injective ι) Q).trans hord
  have hPmem : Affine.genericPoint' hΔ ∉ AddSubgroup.zmultiples Q' :=
    genericPoint'_notMem_zmultiples_ratPointHom hΔ Q
  have hab' : W.toAffine.Nonsingular a b :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hab
  have hAmem : Affine.Point.some a b hab' ∈ AddSubgroup.zmultiples Q :=
    kw_mem_zmultiples_of_abscissa_mem_oddOrderSummingSet_odd hp3 hpodd hord hab' hA
  have hdiff : Affine.genericPoint' hΔ + Affine.mapPoint hΔ hab - Affine.genericPoint' hΔ
      ∈ AddSubgroup.zmultiples Q' := by
    rw [add_sub_cancel_left]
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hAmem
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by
      change n • Q' = ratPointHom (W₀ := W) ι (Affine.Point.some a b hab')
      rw [← hn, ← map_zsmul]⟩
  exact kw_veluDeficit_eq_of_sub_mem_zmultiples_odd hp3 hpodd hord' hPmem hdiff

variable (F : Type*) [Field F] [DecidableEq F] in
theorem kw_veluDeficitFunOrdNonnegAtInftyAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunOrdNonnegAtInftyAt F p := by
  intro W _hΔ x₀ y₀ h₀ hord v hv
  exact ord_veluDeficitFun_nonneg_of_not_isFinitePlace hv
    (kw_isOddVeluSet_oddOrderSummingSet_odd hp3 hpodd hord le_rfl).equation

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F] in
theorem kw_veluDeficitFunKernelTranslationYNotCentreAt_odd
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunKernelTranslationYNotCentreAt F p := by
  intro W hΔ x₀ y₀ h₀ hord v hv ⟨A, hA, hXA⟩
  have := hDD W hΔ
  have hSset := kw_isOddVeluSet_oddOrderSummingSet_odd (W := W) hp3 hpodd hord
    (le_refl ((p - 1) / 2))
  have hAeq : W.toAffine.Equation A.1 A.2 := hSset.equation A hA
  have hAgy : W.veluGy A.1 A.2 ≠ 0 := hSset.gy_ne_zero A hA
  have h2tor : W.toAffine.negY A.1 A.2 ≠ A.2 := negY_ne_self_of_veluGy_ne_zero hAgy
  obtain ⟨b, hab, hXcen, hYcen⟩ := Affine.exists_YClass_negY_notMem_centre hv hAeq h2tor hXA
  exact ⟨A.1, b, hab, ⟨A, hA, rfl⟩, hXcen, hYcen⟩

variable (F : Type*) [Field F] [DecidableEq F] [IsAlgClosed F] in
public theorem kw_veluDeficitFunOrdNonnegAt_odd
    (hDD : ∀ (W : WeierstrassCurve F), W.Δ ≠ 0 → IsDedekindDomain W.toAffine.CoordinateRing)
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitFunOrdNonnegAt F p :=
  veluDeficitFunOrdNonnegAt_of_kernelTranslation_of_atInfty_of_offKernel
    (veluDeficitFunKernelTranslationAt_of_fixes_of_toInfty F
      (kw_veluDeficitFunKernelTranslationFixesAt_odd F hp3 hpodd)
      (veluDeficitFunKernelTranslationToInftyAt_of_yNotCentre F
        (kw_veluDeficitFunKernelTranslationYNotCentreAt_odd F hDD hp3 hpodd)))
    (kw_veluDeficitFunOrdNonnegAtInftyAt_odd F hp3 hpodd)
    (veluDeficitFunOrdNonnegOffKernelAt F p)

end OrdNonneg

section ConstantIsZero

variable {F : Type*} [Field F] [DecidableEq F]

public theorem kw_veluDeficitCrossQuadBetaSqDecompDegLtAt_odd
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) :
    VeluDeficitCrossQuadBetaSqDecompDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  exact ⟨W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly S,
    W.veluDeficitCrossQuadBetaSqSCoeffS2ClearedPoly S,
    hScard ▸ W.veluDeficitCrossQuadBetaSqConstS2ClearedPoly_natDegree_lt hSne,
    fun r s hrs hav => W.veluDeficitCrossQuadBetaSq_mul_prodPow_sDecomp hrs hav⟩

public theorem kw_veluDeficitCrossQuadAlphaBetaDecompDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p)
    (hpodd : Odd p) : VeluDeficitCrossQuadAlphaBetaDecompDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  exact ⟨W.veluDeficitCrossQuadAlphaBetaConstClearedPoly S,
    W.veluDeficitCrossQuadAlphaBetaSCoeffClearedPoly S,
    hScard ▸ W.veluDeficitCrossQuadAlphaBetaConstClearedPoly_natDegree_lt hSne,
    fun r s _hrs hav => W.veluDeficitCrossQuadAlphaBeta_mul_prodPow_sDecomp s hav⟩

public theorem kw_veluDeficitCrossQuadCubeBetaDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hβ : VeluDeficitCrossQuadBetaOnlyDegLtAt F p) :
    VeluDeficitCrossQuadCubeBetaDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  obtain ⟨M, hMdeg, hM⟩ := hβ W hΔ x₀ y₀ h₀ hord
  refine ⟨M - W.veluDeficitCrossQuadAlphaCubeClearedPoly S, ?_, fun r s hrs hav => ?_⟩
  · exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hMdeg
      (hScard ▸ W.veluDeficitCrossQuadAlphaCubeClearedPoly_natDegree_lt hSne))
  · rw [W.veluDeficitCrossQuadCubeBeta_eq_betaOnly_sub_alphaCube, sub_mul,
      W.veluDeficitCrossQuadAlphaCube_mul_prodPow_eq hav, hM hrs hav, eval_sub]

public theorem kw_veluDeficitCrossQuadProdDegLtAt_odd {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p)
    (hCB : VeluDeficitCrossQuadCubeBetaDegLtAt F p) :
    VeluDeficitCrossQuadProdDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  obtain ⟨M, hMdeg, hM⟩ := hCB W hΔ x₀ y₀ h₀ hord
  refine ⟨W.veluDeficitCrossQuadAlphaSqClearedPoly S + M, ?_, fun r s hrs hav => ?_⟩
  · exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt
      (hScard ▸ W.veluDeficitCrossQuadAlphaSqClearedPoly_natDegree_lt hSne) hMdeg)
  · rw [W.veluDeficitCrossQuad_eq_alphaSq_add_cubeBeta, add_mul,
      W.veluDeficitCrossQuadAlphaSq_mul_prodPow_eq hav, hM hrs hav, eval_add]

public theorem kw_veluDeficitCrossQuadBetaOnlyDegLtAt_odd [Infinite F] [IsAlgClosed F] {p : ℕ}
    (hSD : VeluDeficitCrossQuadBetaSDecompDegLtAt F p) :
    VeluDeficitCrossQuadBetaOnlyDegLtAt F p := by
  intro W hΔ x₀ y₀ h₀ hord
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  obtain ⟨M, N, hMdeg, hMN⟩ := hSD W hΔ x₀ y₀ h₀ hord
  have hNgy : ∀ ⦃r s : F⦄, W.toAffine.Equation r s → (∀ A ∈ S, r ≠ A.1) →
      N.eval r * W.veluGy r s = 0 := by
    intro r s hrs hav
    have hrs' : W.toAffine.Equation r (W.toAffine.negY r s) := (Affine.equation_neg r s).mpr hrs
    have hMN' := hMN hrs' hav
    rw [W.veluDeficitCrossQuadBetaOnly_negY_of_equation hrs, hMN hrs hav] at hMN'
    have hgy : s - W.toAffine.negY r s = -W.veluGy r s := by
      simp only [Affine.negY, veluGy]; ring
    linear_combination N.eval r * hgy - hMN'
  have hN2Ψ : N ^ 2 * W.Ψ₂Sq = 0 := by
    refine eq_zero_of_infinite_isRoot _ ?_
    have hbad_fin : {r : F | ∃ A ∈ S, r = A.1}.Finite :=
      (S.finite_toSet.image Prod.fst).subset (by rintro r ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩)
    refine hbad_fin.infinite_compl.mono ?_
    intro r hr
    have hav : ∀ A ∈ S, r ≠ A.1 := fun A hA heq => hr ⟨A, hA, heq⟩
    obtain ⟨s, hrs⟩ := Affine.exists_equation_of_isAlgClosed W r
    have hsq : (N.eval r) ^ 2 * W.Ψ₂Sq.eval r = 0 := by
      rw [← W.veluU_eq_Ψ₂Sq_eval hrs, veluU, ← mul_pow, hNgy hrs hav, zero_pow two_ne_zero]
    simpa [IsRoot, eval_mul, eval_pow] using hsq
  have hN0 : N = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp
      ((mul_eq_zero.mp hN2Ψ).resolve_right (W.Ψ₂Sq_ne_zero_of_Δ_ne_zero hΔ))
  exact ⟨M, hMdeg, fun r s hrs hav => by rw [hMN hrs hav, hN0, eval_zero, zero_mul, add_zero]⟩

public theorem kw_veluDeficitConstantIsZeroAt_odd [Infinite F] [IsAlgClosed F]
    {p : ℕ} (hp3 : 3 ≤ p) (hpodd : Odd p) (hCQ : VeluDeficitCrossQuadProdDegLtAt F p) :
    VeluDeficitConstantIsZeroAt F p := by
  intro W hΔ x₀ y₀ h₀ hord c hc
  have hodd : p % 2 = 1 := Nat.odd_iff.mp hpodd
  set S := W.oddOrderSummingSet (Point.some x₀ y₀ h₀) ((p - 1) / 2)
  have hScard : S.card = (p - 1) / 2 := kw_card_oddOrderSummingSet_odd hp3 hpodd hord le_rfl
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; omega)
  have hSeq : ∀ A ∈ S, W.toAffine.Equation A.1 A.2 :=
    (kw_isOddVeluSet_oddOrderSummingSet_odd hp3 hpodd hord le_rfl).equation
  obtain ⟨M, hMdeg, hM⟩ := hCQ W hΔ x₀ y₀ h₀ hord
  exact W.veluDeficit_isConstant_constant_eq_zero_of_crossQuadProdDegLt hSne hSeq
    (Affine.exists_equation_of_isAlgClosed W) hc (M := M) (hScard ▸ hMdeg)
    (fun r s hrs hav => hM hrs hav)

end ConstantIsZero

end WeierstrassCurve

end

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end privateSection
