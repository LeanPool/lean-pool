/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Derivation
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The derivative on a fraction field

`IsFractionRing.deriv D` extends a map `D : R → R` on a domain `R` to any fraction field
`K` of `R` by the quotient rule. When `D` is additive and satisfies the Leibniz rule, the
extension is representation-independent (`IsFractionRing.deriv_div`), extends `D`
(`IsFractionRing.deriv_algebraMap`), and is itself additive and Leibniz
(`IsFractionRing.deriv_add`, `IsFractionRing.deriv_mul`). Both `RatFunc.derivative`
(`upstream HyperellipticCurves.Archive.RatFuncDerivative`) and the `z`-derivative on `Frac(K⟦z⟧)`
used to
differentiate disk expansions of curve functions are instances.
-/

@[expose] public section

namespace IsFractionRing

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of a domain stays nonzero in a fraction field. -/
theorem algebraMap_ne_zero {c : R} (hc : c ≠ 0) : algebraMap R K c ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc

variable [IsDomain R] (D : R → R)

/-- Every element of a fraction field is a fraction of ring elements (with nonzero
denominator), in `∃`-form suitable for `obtain ⟨p, q, hq, rfl⟩` destructuring. -/
theorem exists_eq_div (x : K) :
    ∃ p q : R, q ≠ 0 ∧ x = algebraMap R K p / algebraMap R K q := by
  obtain ⟨p, q, hq, h⟩ := IsFractionRing.div_surjective (A := R) x
  exact ⟨p, q, nonZeroDivisors.ne_zero hq, h.symm⟩

/-- The extension of a map `D : R → R` to a fraction field by the quotient rule, via a
chosen fraction representation. When `D` is additive and satisfies the Leibniz rule, the
value is independent of the representation (`IsFractionRing.deriv_div`), `deriv D` extends
`D` (`IsFractionRing.deriv_algebraMap`) and is itself additive and Leibniz
(`IsFractionRing.deriv_add`, `IsFractionRing.deriv_mul`). -/
noncomputable def deriv (x : K) : K :=
  (algebraMap R K (D (IsLocalization.sec (nonZeroDivisors R) x).1)
      * algebraMap R K ((IsLocalization.sec (nonZeroDivisors R) x).2 : R)
    - algebraMap R K (IsLocalization.sec (nonZeroDivisors R) x).1
      * algebraMap R K (D ((IsLocalization.sec (nonZeroDivisors R) x).2 : R)))
    / algebraMap R K (((IsLocalization.sec (nonZeroDivisors R) x).2 : R) ^ 2)

variable {D}
variable (hadd : ∀ p q, D (p + q) = D p + D q)
  (hmul : ∀ p q, D (p * q) = D p * q + p * D q)

include hmul in
/-- The quotient rule holds for every fraction representation. -/
theorem deriv_div (p : R) {q : R} (hq : q ≠ 0) :
    deriv D (algebraMap R K p / algebraMap R K q)
      = (algebraMap R K (D p) * algebraMap R K q - algebraMap R K p * algebraMap R K (D q))
        / algebraMap R K (q ^ 2) := by
  set x := algebraMap R K p / algebraMap R K q with hx
  set r := (IsLocalization.sec (nonZeroDivisors R) x).1 with hr
  set t := ((IsLocalization.sec (nonZeroDivisors R) x).2 : R) with ht
  have ht0 : t ≠ 0 :=
    nonZeroDivisors.ne_zero (IsLocalization.sec (nonZeroDivisors R) x).2.2
  have hspec : x * algebraMap R K t = algebraMap R K r :=
    IsLocalization.sec_spec (nonZeroDivisors R) x
  have hqz : algebraMap R K q ≠ 0 := algebraMap_ne_zero hq
  have hcross : p * t = r * q := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul]
    rw [hx, div_mul_eq_mul_div, div_eq_iff hqz] at hspec
    linear_combination hspec
  have hdiff : D p * t + p * D t = D r * q + r * D q := by
    have h := congrArg D hcross
    rwa [hmul, hmul] at h
  rw [deriv, ← hr, ← ht, div_eq_div_iff (algebraMap_ne_zero (pow_ne_zero 2 ht0))
    (algebraMap_ne_zero (pow_ne_zero 2 hq))]
  simp only [← map_mul, ← map_sub]
  refine congrArg _ ?_
  linear_combination (D q * t + q * D t) * hcross - (q * t) * hdiff

include hmul in
/-- `deriv D` extends `D`. -/
theorem deriv_algebraMap (c : R) : deriv D (algebraMap R K c) = algebraMap R K (D c) := by
  have hone : D 1 = 0 := by
    have h := hmul 1 1
    simp only [mul_one, one_mul] at h
    exact left_eq_add.mp h
  have h : algebraMap R K c = algebraMap R K c / algebraMap R K 1 := by rw [map_one, div_one]
  rw [h, deriv_div hmul c one_ne_zero, hone]
  simp

include hmul in
/-- Leibniz rule for `deriv D`. -/
theorem deriv_mul (x y : K) : deriv D (x * y) = deriv D x * y + x * deriv D y := by
  obtain ⟨p, q, hq, rfl⟩ := exists_eq_div (R := R) x
  obtain ⟨r, s, hs, rfl⟩ := exists_eq_div (R := R) y
  have hqz : algebraMap R K q ≠ 0 := algebraMap_ne_zero hq
  have hsz : algebraMap R K s ≠ 0 := algebraMap_ne_zero hs
  have hmul' : algebraMap R K p / algebraMap R K q * (algebraMap R K r / algebraMap R K s)
      = algebraMap R K (p * r) / algebraMap R K (q * s) := by
    rw [map_mul, map_mul, div_mul_div_comm]
  rw [hmul', deriv_div hmul _ (mul_ne_zero hq hs), deriv_div hmul p hq, deriv_div hmul r hs]
  field_simp
  simp only [← map_mul, ← map_sub, ← map_add]
  refine congrArg _ ?_
  simp only [hmul]
  ring

include hadd hmul in
/-- Additivity of `deriv D`. -/
theorem deriv_add (x y : K) : deriv D (x + y) = deriv D x + deriv D y := by
  obtain ⟨p, q, hq, rfl⟩ := exists_eq_div (R := R) x
  obtain ⟨r, s, hs, rfl⟩ := exists_eq_div (R := R) y
  have hqz : algebraMap R K q ≠ 0 := algebraMap_ne_zero hq
  have hsz : algebraMap R K s ≠ 0 := algebraMap_ne_zero hs
  have hadd' : algebraMap R K p / algebraMap R K q + algebraMap R K r / algebraMap R K s
      = algebraMap R K (p * s + q * r) / algebraMap R K (q * s) := by
    rw [div_add_div _ _ hqz hsz, ← map_mul, ← map_mul, ← map_mul, ← map_add]
  rw [hadd', deriv_div hmul _ (mul_ne_zero hq hs), deriv_div hmul p hq, deriv_div hmul r hs]
  rw [div_add_div _ _ (algebraMap_ne_zero (pow_ne_zero 2 hq))
    (algebraMap_ne_zero (pow_ne_zero 2 hs))]
  simp only [← map_mul, ← map_sub, ← map_add]
  rw [div_eq_div_iff (algebraMap_ne_zero (pow_ne_zero 2 (mul_ne_zero hq hs)))
    (algebraMap_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hs))),
    ← map_mul, ← map_mul]
  refine congrArg _ ?_
  simp only [hmul, hadd]
  ring

section Derivation

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra S K] [IsScalarTower S R K]

/-- The extension of a derivation on a domain to a fraction field, by the quotient rule. -/
noncomputable def derivation (d : Derivation S R R) : Derivation S K K where
  toFun := deriv (d ·)
  map_add' := deriv_add (fun p q ↦ d.map_add p q) d.leibniz_mul
  map_smul' s x := by
    have h0 : deriv (K := K) (d ·) (algebraMap S K s) = 0 := by
      rw [IsScalarTower.algebraMap_apply S R K, deriv_algebraMap d.leibniz_mul,
        Derivation.map_algebraMap, map_zero]
    rw [Algebra.smul_def, deriv_mul d.leibniz_mul, h0, zero_mul, zero_add,
      RingHom.id_apply, Algebra.smul_def]
  map_one_eq_zero' := by
    have h := deriv_algebraMap (K := K) (D := (d ·)) d.leibniz_mul 1
    simpa using h
  leibniz' x y := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, deriv_mul d.leibniz_mul, smul_eq_mul, smul_eq_mul]
    ring

@[simp]
theorem derivation_apply (d : Derivation S R R) (x : K) :
    derivation d x = deriv (d ·) x :=
  rfl

/-- `IsFractionRing.derivation` extends the derivation. -/
theorem derivation_algebraMap (d : Derivation S R R) (r : R) :
    derivation d (algebraMap R K r) = algebraMap R K (d r) :=
  deriv_algebraMap d.leibniz_mul r

end Derivation

end IsFractionRing

end
