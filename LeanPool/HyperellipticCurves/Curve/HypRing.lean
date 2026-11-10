/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.QuadraticAlgebra
public import LeanPool.HyperellipticCurves.ForMathlib.RatFunc

import Mathlib.FieldTheory.KummerPolynomial

/-!
# Coordinate ring and function field of an odd-degree hyperelliptic curve

For a commutative ring `R` and `f : R[X]` we define `ChabautyColeman.HypRing R f`, the
affine coordinate ring `R[x][Y]/(Y² - f)` of the curve `y² = f(x)`, and for a field `K`
`ChabautyColeman.HypField K f`, the corresponding object `K(x)[Y]/(Y² - f)` over the
rational function field (an actual field once `Y² - f` is irreducible, which holds for
`f` of odd degree; see `lem:hyp-irred` in the blueprint).

Both are implemented via `QuadraticAlgebra ⬝ f 0`, the free rank-2 algebra with basis
`(1, ω)` and `ω² = f`: this makes the basis `(1, y)` definitional and gives the
hyperelliptic involution `ι` as the `star` operation of the `StarRing` structure, with
norm form API (`QuadraticAlgebra.norm`) for free.

Blueprint node: `def:hypring`.
-/

@[expose] public section

open Polynomial


namespace ChabautyColeman

open QuadraticAlgebra

/-- The affine coordinate ring `R[x][Y]/(Y² - f)` of the hyperelliptic curve `y² = f(x)`
over `R`, as the free rank-2 algebra `R[x] ⊕ R[x]·y` with `y² = f`. -/
abbrev HypRing (R : Type*) [CommRing R] (f : R[X]) : Type _ :=
  QuadraticAlgebra R[X] f 0

/-- The algebra `K(x)[Y]/(Y² - f)` associated to the hyperelliptic curve `y² = f(x)`
over the field `K`; it is the function field of the curve once `Y² - f` is irreducible
over `K(x)`, e.g. for `f` of odd degree. -/
abbrev HypField (K : Type*) [Field K] (f : K[X]) : Type _ :=
  QuadraticAlgebra (RatFunc K) (algebraMap K[X] (RatFunc K) f) 0

/-! ### Irreducibility of `Y² - f` for `f` of odd degree (blueprint node `lem:hyp-irred`)

For `f` of odd degree, `f` is not a square in `K(x)`, so `Y² - f` is irreducible over
`K(x)`. Consequently `HypField K f` is a field (this is Mathlib's
`QuadraticAlgebra` field instance, available under `Fact (Odd f.natDegree)` via
`instFactHypField` below), quadratic over `K(x)` (`QuadraticAlgebra.finrank_eq_two`),
and `HypRing K f` is a domain, embedding into `HypField K f` via `HypRing.toHypField`.
-/

section HypIrred

variable {K : Type*} [Field K] (f : K[X])

theorem not_isSquare_algebraMap_ratFunc (hf : Odd f.natDegree) :
    ¬IsSquare (algebraMap K[X] (RatFunc K) f) :=
  RatFunc.not_isSquare_of_odd_intDegree (by rwa [RatFunc.intDegree_polynomial, Int.odd_coe_nat])

/-- For `f : K[X]` of odd degree, the polynomial `Y² - f` is irreducible over `K(x)`. -/
theorem irreducible_Ysq_sub_f (hf : Odd f.natDegree) :
    Irreducible (X ^ 2 - C (algebraMap K[X] (RatFunc K) f) : (RatFunc K)[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two
    fun r hr ↦ not_isSquare_algebraMap_ratFunc f hf ⟨r, by rw [← hr, sq]⟩

/-- For `f` of odd degree, the defining quadratic of `HypField K f` has no root in `K(x)`;
this `Fact` feeds the generic `Field (QuadraticAlgebra K a b)` instance from Mathlib,
so `Field (HypField K f)` is available whenever `Fact (Odd f.natDegree)` is. -/
instance instFactHypField [hf : Fact (Odd f.natDegree)] :
    Fact (∀ r : RatFunc K, r ^ 2 ≠ algebraMap K[X] (RatFunc K) f + 0 * r) :=
  ⟨fun r hr ↦ not_isSquare_algebraMap_ratFunc f hf.out
    ⟨r, by rw [← sq, hr, zero_mul, add_zero]⟩⟩

namespace HypRing

/-- The canonical embedding of the coordinate ring into `K(x)[Y]/(Y² - f)`,
as a `K[x]`-algebra homomorphism. -/
noncomputable def toHypField : HypRing K f →ₐ[K[X]] HypField K f where
  toRingHom := mapRingHomTo (algebraMap K[X] (RatFunc K)) rfl (map_zero _)
  commutes' p := by ext <;> simp

@[simp]
theorem re_toHypField (z : HypRing K f) :
    (toHypField f z).re = algebraMap K[X] (RatFunc K) z.re := rfl

@[simp]
theorem im_toHypField (z : HypRing K f) :
    (toHypField f z).im = algebraMap K[X] (RatFunc K) z.im := rfl

theorem toHypField_injective : Function.Injective (toHypField f) :=
  mapRingHomTo_injective (RatFunc.algebraMap_injective K) rfl (map_zero _)

/-- The coordinate ring of `y² = f(x)` over a field is a domain for `f` of odd degree. -/
instance instIsDomain [Fact (Odd f.natDegree)] : IsDomain (HypRing K f) :=
  (toHypField_injective f).isDomain (toHypField f).toRingHom

end HypRing

end HypIrred

namespace HypRing

variable {R : Type*} [CommRing R] (f : R[X])

/-- The distinguished square root `y` of `f` in the coordinate ring. -/
noncomputable abbrev y : HypRing R f := ω

@[simp]
theorem y_sq : y f ^ 2 = algebraMap R[X] _ f := by rw [omega_sq]; simp

@[simp]
theorem star_y : star (y f) = -y f := by rw [star_omega]; simp

/-- The involution negates the imaginary part (the `b = 0` case of
`QuadraticAlgebra.star_mk`). -/
@[simp]
theorem star_mk (p q : R[X]) : star (⟨p, q⟩ : HypRing R f) = ⟨p, -q⟩ := by simp

/-- Every element of the coordinate ring decomposes as `re + im · y`. -/
theorem eq_algebraMap_re_add_im (z : HypRing R f) :
    z = algebraMap R[X] (HypRing R f) z.re + algebraMap R[X] (HypRing R f) z.im * y f := by
  have hmk := QuadraticAlgebra.mk_eq_add_smul_omega (R := R[X]) (a := f) (b := 0) z.re z.im
  rwa [Algebra.smul_def] at hmk

/-- The hyperelliptic involution `ι` on the coordinate ring, as an `R[x]`-algebra
automorphism; it is given by the `star` operation, `a + b·y ↦ a - b·y`. -/
noncomputable def iota : HypRing R f ≃ₐ[R[X]] HypRing R f := starAlgEquiv

@[simp]
theorem iota_apply (z : HypRing R f) : iota f z = star z := rfl

@[simp]
theorem iota_symm : (iota f).symm = iota f := rfl

theorem iota_y : iota f (y f) = -y f := by simp

/-! Norm form and trace on the coordinate ring (blueprint node `lem:normform`):
for `α = a + b·y` one has `Nm(α) = α·ι(α) = a² - b²·f` and `Tr(α) = 2a`. -/

theorem norm_eq (z : HypRing R f) :
    Algebra.norm R[X] z = z.re ^ 2 - f * z.im ^ 2 := by
  rw [algebraNorm_eq_norm, norm_def]
  ring

theorem trace_eq (z : HypRing R f) : Algebra.trace R[X] (HypRing R f) z = 2 * z.re := by
  rw [algebraTrace_eq]
  ring

theorem mul_star_eq_norm (z : HypRing R f) :
    z * star z = algebraMap R[X] _ (Algebra.norm R[X] z) := by
  rw [algebraNorm_eq_norm, algebraMap_norm_eq_mul_star]

end HypRing

namespace HypField

variable {K : Type*} [Field K] (f : K[X])

/-- The distinguished square root `y` of `f` in `K(x)[Y]/(Y² - f)`. -/
noncomputable abbrev y : HypField K f := ω

@[simp]
theorem y_sq : y f ^ 2 = algebraMap K[X] _ f := by
  rw [omega_sq, IsScalarTower.algebraMap_apply K[X] (RatFunc K) (HypField K f)]; simp

@[simp]
theorem star_y : star (y f) = -y f := by rw [star_omega]; simp

/-- The hyperelliptic involution `ι` on `K(x)[Y]/(Y² - f)`, as a `K(x)`-algebra
automorphism; it is given by the `star` operation, `a + b·y ↦ a - b·y`. -/
noncomputable def iota : HypField K f ≃ₐ[RatFunc K] HypField K f := starAlgEquiv

@[simp]
theorem iota_apply (z : HypField K f) : iota f z = star z := rfl

@[simp]
theorem iota_symm : (iota f).symm = iota f := rfl

theorem iota_y : iota f (y f) = -y f := by simp

/-! Norm form and trace on the function field (blueprint node `lem:normform`):
for `α = a + b·y ∈ F_K` one has `Nm(α) = α·ι(α) = a² - b²·f` and `Tr(α) = 2a`. -/

theorem norm_eq (z : HypField K f) :
    Algebra.norm (RatFunc K) z = z.re ^ 2 - algebraMap K[X] (RatFunc K) f * z.im ^ 2 := by
  rw [algebraNorm_eq_norm, norm_def]
  ring

theorem trace_eq (z : HypField K f) :
    Algebra.trace (RatFunc K) (HypField K f) z = 2 * z.re := by
  rw [algebraTrace_eq]
  ring

theorem mul_star_eq_norm (z : HypField K f) :
    z * star z = algebraMap (RatFunc K) _ (Algebra.norm (RatFunc K) z) := by
  rw [algebraNorm_eq_norm, algebraMap_norm_eq_mul_star]

end HypField

section

variable {K : Type*} [Field K] (f : K[X])

/-- The embedding of the coordinate ring into `F_K`, in terms of the basis `(1, y)`. -/
theorem HypRing.toHypField_apply (w : HypRing K f) :
    HypRing.toHypField f w = algebraMap K[X] _ w.re + algebraMap K[X] _ w.im * HypField.y f := by
  ext <;> simp

end

/-! ### Units of the coordinate ring (blueprint node `lem:hypring-units`) -/

namespace HypRing

variable {K : Type*} [Field K] {f : K[X]}

/-- If `a² = C c + f·b²` with `f` of odd degree, then `b = 0`: otherwise `f·b²` has odd
degree while `a²` has even degree. -/
theorem eq_zero_of_sq_eq_C_add_mul_sq (hf : Odd f.natDegree) {a b : K[X]} {c : K}
    (h1 : a ^ 2 = C c + f * b ^ 2) : b = 0 := by
  have hf0 : f ≠ 0 := fun h ↦ by simp [h, Nat.odd_iff] at hf
  by_contra hb
  obtain ⟨k, hk⟩ := hf
  have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hmul : (f * b ^ 2).natDegree = f.natDegree + 2 * b.natDegree := by
    rw [natDegree_mul hf0 hb2, natDegree_pow]
  have hR : (C c + f * b ^ 2).natDegree = f.natDegree + 2 * b.natDegree := by
    rw [natDegree_add_eq_right_of_natDegree_lt (by rw [natDegree_C, hmul]; lia), hmul]
  have hL := congrArg natDegree h1
  rw [natDegree_pow, hR] at hL
  lia

/-- The units of the coordinate ring are the nonzero constants: `(A_K)ˣ = Kˣ`
for `f` of odd degree (no assumption on the characteristic is needed):
the norm of a unit is a unit `a² - b²·f` of `K[x]`, and `b ≠ 0` would force the
odd degree of `b²·f` to equal the even degree of `a²`. -/
theorem isUnit_iff (hf : Odd f.natDegree) {z : HypRing K f} :
    IsUnit z ↔ ∃ c : Kˣ, z = algebraMap K (HypRing K f) c := by
  refine ⟨fun hz ↦ ?_, fun ⟨c, hc⟩ ↦ hc ▸ c.isUnit.map (algebraMap K (HypRing K f))⟩
  have hn : IsUnit (z.re ^ 2 - f * z.im ^ 2) := by
    have h := isUnit_iff_norm_isUnit.mp hz
    rwa [← algebraNorm_eq_norm, norm_eq] at h
  obtain ⟨c, hc, hcp⟩ := Polynomial.isUnit_iff.mp hn
  have h1 : z.re ^ 2 = C c + f * z.im ^ 2 := by linear_combination -hcp
  have him : z.im = 0 := eq_zero_of_sq_eq_C_add_mul_sq hf h1
  have hre : IsUnit z.re := by
    refine (isUnit_pow_iff two_ne_zero).mp ?_
    have h2 : C c = z.re ^ 2 := by rw [hcp, him]; ring
    exact h2 ▸ hc.map C
  obtain ⟨r, hr, hrp⟩ := Polynomial.isUnit_iff.mp hre
  refine ⟨hr.unit, ?_⟩
  ext
  · simp [← hrp, Polynomial.algebraMap_eq]
  · simp [him]

end HypRing

/-! ### Denominator clearing: `F_K` is the fraction field of the coordinate ring -/

section Bezout

variable {K : Type*} [Field K] {f : K[X]}

/-- **Coprime denominators clear completely**: if `s·x` and `s′·x` both lie in the
coordinate ring and `s`, `s′` satisfy a Bézout relation there, then `x` itself lies in
the coordinate ring — it has no affine poles at all. -/
theorem toHypField_eq_of_bezout {x : HypField K f} {s s' α β w w' : HypRing K f}
    (hbez : α * s + β * s' = 1)
    (hw : HypRing.toHypField f s * x = HypRing.toHypField f w)
    (hw' : HypRing.toHypField f s' * x = HypRing.toHypField f w') :
    x = HypRing.toHypField f (α * w + β * w') := by
  have h := congrArg (HypRing.toHypField f) hbez
  rw [map_add, map_mul, map_mul, map_one] at h
  rw [map_add, map_mul, map_mul, ← hw, ← hw']
  linear_combination -x * h

end Bezout

namespace HypRing

variable {K : Type*} [Field K] (f : K[X])

/-- **The function field is the fraction field of the coordinate ring, constructively**:
every element of `F_K` admits a denominator-clearing certificate `s·ξ = w` over
`HypRing K f` with `s ≠ 0` (clear the denominators of the two `K(x)`-components). -/
theorem exists_toHypField_mul_eq (ξ : HypField K f) :
    ∃ s w : HypRing K f, toHypField f s ≠ 0 ∧ toHypField f s * ξ = toHypField f w := by
  have hd : ξ.re.denom * ξ.im.denom ≠ 0 :=
    mul_ne_zero ξ.re.denom_ne_zero ξ.im.denom_ne_zero
  refine ⟨algebraMap K[X] _ (ξ.re.denom * ξ.im.denom),
    ⟨ξ.re.num * ξ.im.denom, ξ.im.num * ξ.re.denom⟩, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (toHypField_injective f)).mpr
      ((map_ne_zero_iff _ QuadraticAlgebra.algebraMap_injective).mpr hd)
  · have key (r : RatFunc K) : r * algebraMap K[X] (RatFunc K) r.denom
        = algebraMap K[X] (RatFunc K) r.num :=
      ((div_eq_iff (RatFunc.algebraMap_ne_zero r.denom_ne_zero)).mp r.num_div_denom).symm
    ext
    · rw [QuadraticAlgebra.re_mul, re_toHypField, im_toHypField, re_toHypField]
      simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
      push_cast [map_mul]
      linear_combination algebraMap K[X] (RatFunc K) ξ.im.denom * key ξ.re
    · rw [QuadraticAlgebra.im_mul, re_toHypField, im_toHypField, im_toHypField]
      simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
      push_cast [map_mul]
      linear_combination algebraMap K[X] (RatFunc K) ξ.re.denom * key ξ.im

/-- Common-denominator form of `ChabautyColeman.HypRing.exists_toHypField_mul_eq`: a
finite family of function-field elements admits a single clearing denominator. -/
theorem exists_toHypField_mul_eq_finite [Fact (Odd f.natDegree)] {ι : Type*} [Finite ι]
    (ξ : ι → HypField K f) :
    ∃ (s : HypRing K f) (w : ι → HypRing K f), toHypField f s ≠ 0
      ∧ ∀ i, toHypField f s * ξ i = toHypField f (w i) := by
  classical
  have := Fintype.ofFinite ι
  choose sj wj hsj hswj using fun i ↦ exists_toHypField_mul_eq f (ξ i)
  refine ⟨∏ i, sj i, fun i ↦ wj i * ∏ j ∈ Finset.univ.erase i, sj j, ?_, fun i ↦ ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hsj i
  · rw [map_prod, map_mul, map_prod,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    linear_combination (∏ j ∈ Finset.univ.erase i, toHypField f (sj j)) * hswj i

end HypRing

end ChabautyColeman

end
