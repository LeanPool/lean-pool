/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.Charts
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse

import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries

/-!
# Expansions of differentials on disks and their antiderivatives

For a differential `ω = h(x) dx/y` with `h ∈ O[x]` (`deg h ≤ g - 1`) and each disk of
`ChabautyColeman.diskParamGeneric`/`diskParamWeierstrass`, the restriction `ω|_D` is `w_D(z) dz`
with `w_D ∈ O⟦z⟧`.

**Generic disk** `D_(ā, b_bar)`, parametrized by `z ↦ (a + z, b · η(z))`: since `x = a + z` gives
`dx = dz` and `y = b · η(z)`, `w_D(z) = h(a + z) · b⁻¹ · η(z)⁻¹`
(`ChabautyColeman.omegaExpansionGeneric`), integral because `η(0) = 1` and `b` is a unit; the
defining relation is `(b · η(z)) · w_D(z) = h(a + z)`
(`ChabautyColeman.yseries_mul_omegaExpansionGeneric`).

**Weierstrass disk** `D_(ω_bar, 0)`, parametrized by `z = y`: the coordinate `x(z)`
(`ChabautyColeman.weierstrassSeries`) is the Hensel root of `f(x) = z²` with `x ≡ ω`, obtained
as the Weierstrass root over the `X`-adically complete ring `O⟦z⟧` (no completeness of `O`
needed). Then
`w_D(z) = 2·h(x(z))·f'(x(z))⁻¹` (`ChabautyColeman.omegaExpansionWeierstrass`), pole-free since
`f'(x(z))` is a unit; the differential relation `z · w_D(z) = h(x(z)) · x'(z)`
(`ChabautyColeman.X_mul_omegaExpansionWeierstrass`) follows from the chain rule applied to
`f(x(z)) = z²`.

The **disk antiderivative** `G^ω_D(z) := ∑ (w_D)_k/(k + 1) · z^(k+1)` (with `G(0) = 0`) is the
formal antiderivative (`ChabautyColeman.antideriv`) of `w_D` over the fraction field; it is a
right inverse of the formal derivative (`ChabautyColeman.derivative_antideriv`).

The infinity chart and the reduction/order-matching statements are developed elsewhere.

Blueprint nodes: `lem:omega-expansion` (generic and Weierstrass charts), `def:disk-antider`.
-/

@[expose] public section

open PowerSeries IsLocalRing Polynomial

namespace ChabautyColeman

variable {O : Type*} [CommRing O]

/-! ### The generic-disk expansion of `h(x) dx/y` -/

/-- The expansion of the differential `h(x) dx/y` on the generic disk at `(a, b)`:
the power series `w_D(z) = h(a + z) · b⁻¹ · η(z)⁻¹`, where `η = diskSeriesGeneric f a`
(so on the disk `x = a + z`, `dx = dz`, and `y = b · η(z)`). Since `η(0) = 1` and `b` is a
unit (genericity `b_bar ≠ 0`), this lies in `O⟦z⟧`. -/
noncomputable def omegaExpansionGeneric (f h : O[X]) (a b : O) : O⟦X⟧ :=
  (taylor a h : O⟦X⟧) * PowerSeries.C (Ring.inverse b) * invOfUnit (diskSeriesGeneric f a) 1

@[simp] theorem constantCoeff_omegaExpansionGeneric (f h : O[X]) (a b : O) :
    constantCoeff (omegaExpansionGeneric f h a b) = h.eval a * Ring.inverse b := by
  rw [omegaExpansionGeneric, map_mul, map_mul, constantCoeff_invOfUnit,
    ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, taylor_coeff_zero,
    constantCoeff_C, inv_one, Units.val_one, mul_one]

/-- Cleared-denominator form of the generic expansion: `(b · η(z)) · w_D(z) = h(a + z)`
as power series, i.e. `w_D dz = h(x) dx/y` with `x = a + z` (so `dx = dz`) and
`y = b · η(z)`. -/
theorem yseries_mul_omegaExpansionGeneric (f h : O[X]) {a b : O} (hb : IsUnit b) :
    (PowerSeries.C b * diskSeriesGeneric f a) * omegaExpansionGeneric f h a b
      = (taylor a h : O⟦X⟧) := by
  have hη : diskSeriesGeneric f a * invOfUnit (diskSeriesGeneric f a) 1 = 1 :=
    mul_invOfUnit _ 1 (by rw [constantCoeff_diskSeriesGeneric, Units.val_one])
  rw [omegaExpansionGeneric]
  calc PowerSeries.C b * diskSeriesGeneric f a
          * ((taylor a h : O⟦X⟧) * PowerSeries.C (Ring.inverse b)
              * invOfUnit (diskSeriesGeneric f a) 1)
      = (taylor a h : O⟦X⟧) * (PowerSeries.C b * PowerSeries.C (Ring.inverse b))
          * (diskSeriesGeneric f a * invOfUnit (diskSeriesGeneric f a) 1) := by ring
    _ = (taylor a h : O⟦X⟧) := by
        rw [← map_mul, Ring.mul_inverse_cancel _ hb, map_one, hη, mul_one, mul_one]

/-- The generic-disk expansion is additive in the numerator (`(h₁ + h₂)·dx/y` expands to the
sum). -/
theorem omegaExpansionGeneric_add (f p q : O[X]) (a b : O) :
    omegaExpansionGeneric f (p + q) a b
      = omegaExpansionGeneric f p a b + omegaExpansionGeneric f q a b := by
  simp only [omegaExpansionGeneric, map_add, Polynomial.coe_add, add_mul]

/-- The generic-disk expansion is homogeneous in the numerator (`(c·h)·dx/y`). -/
theorem omegaExpansionGeneric_smul (c : O) (f p : O[X]) (a b : O) :
    omegaExpansionGeneric f (c • p) a b = c • omegaExpansionGeneric f p a b := by
  simp only [omegaExpansionGeneric, map_smul, Polynomial.coe_smul, smul_mul_assoc]

/-- **The generic-disk differential expansion is injective in the numerator**: a differential
`h·dx/y` is determined by its expansion at an affine non-Weierstrass point (needs `b` a unit).
The building block for recovering the numerator of a regular differential from its disk
expansion. -/
theorem omegaExpansionGeneric_injective {f : O[X]} {a b : O} (hb : IsUnit b) {p q : O[X]}
    (heq : omegaExpansionGeneric f p a b = omegaExpansionGeneric f q a b) : p = q := by
  have key : (taylor a p : O⟦X⟧) = (taylor a q : O⟦X⟧) := by
    rw [← yseries_mul_omegaExpansionGeneric f p hb, ← yseries_mul_omegaExpansionGeneric f q hb,
      heq]
  exact taylor_injective a (mod_cast key)

/-! ### The Weierstrass-disk expansion of `h(x) dx/y` -/

/-- Existence of the Weierstrass coordinate power series `x(z) ∈ O⟦z⟧` with `f(x(z)) = z²` and
`x(z) ≡ ω mod z`, as the Hensel root of `f(x) - z²` in the `X`-adically complete ring `O⟦z⟧`. -/
theorem exists_weierstrassSeries {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    ∃ x : O⟦X⟧, aeval x f = PowerSeries.X ^ 2 ∧
      x - PowerSeries.C ω ∈ Ideal.span {(PowerSeries.X : O⟦X⟧)} := by
  let φ : O →+* O⟦X⟧ := algebraMap O (O⟦X⟧)
  have hφinj : Function.Injective φ := PowerSeries.C_injective
  set I : Ideal (O⟦X⟧) := Ideal.span {(PowerSeries.X : O⟦X⟧)} with hI
  set g : (O⟦X⟧)[X] := f.map φ - Polynomial.C ((PowerSeries.X : O⟦X⟧) ^ 2) with hg
  have hmon : g.Monic := (hf.map φ).sub_of_left <| degree_C_le.trans_lt
    (natDegree_pos_iff_degree_pos.mp (by rwa [natDegree_map_eq_of_injective hφinj f]))
  have hXmem : (PowerSeries.X : O⟦X⟧) ^ 2 ∈ I := by
    rw [hI, Ideal.mem_span_singleton]; exact ⟨PowerSeries.X, sq PowerSeries.X⟩
  have heval : g.eval (φ ω) ∈ I := by
    rw [hg, eval_sub, eval_C, eval_map_apply, hω, map_zero, zero_sub]
    exact neg_mem hXmem
  have hderiv : IsUnit (Ideal.Quotient.mk I (g.derivative.eval (φ ω))) := by
    have he : g.derivative.eval (φ ω) = φ (f.derivative.eval ω) := by
      rw [hg, derivative_sub, Polynomial.derivative_C, sub_zero, derivative_map, eval_map_apply]
    rw [he]
    exact (hu.map φ).map (Ideal.Quotient.mk I)
  obtain ⟨x, hx1, hx2⟩ := HenselianRing.is_henselian g hmon (φ ω) heval hderiv
  rw [IsRoot, hg, eval_sub, eval_C, sub_eq_zero, eval_map, ← aeval_def] at hx1
  exact ⟨x, hx1, hx2⟩

/-- The Weierstrass-disk coordinate power series `x(z)`: the Hensel root of `f(x) = z²` congruent
to `ω`, with `z = y` the disk parameter. -/
noncomputable def weierstrassSeries {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) : O⟦X⟧ :=
  (exists_weierstrassSeries hf hdeg hω hu).choose

theorem weierstrassSeries_eval {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O}
    (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    aeval (weierstrassSeries hf hdeg hω hu) f = PowerSeries.X ^ 2 :=
  (exists_weierstrassSeries hf hdeg hω hu).choose_spec.1

@[simp] theorem constantCoeff_weierstrassSeries {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    constantCoeff (weierstrassSeries hf hdeg hω hu) = ω := by
  have h0 := PowerSeries.X_dvd_iff.mp
    (Ideal.mem_span_singleton.mp (exists_weierstrassSeries hf hdeg hω hu).choose_spec.2)
  rwa [map_sub, constantCoeff_C, sub_eq_zero] at h0

/-- `f'(x(z))` is a unit in `O⟦z⟧` (its constant coefficient is `f'(ω)`, a unit). -/
theorem isUnit_aeval_deriv_weierstrassSeries {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    IsUnit (aeval (weierstrassSeries hf hdeg hω hu) f.derivative) := by
  rw [isUnit_iff_constantCoeff, PowerSeries.constantCoeff_aeval,
    constantCoeff_weierstrassSeries]
  exact hu

/-- The chain rule at the Weierstrass series: `f'(x(z)) · x'(z) = 2z`, from differentiating
`f(x(z)) = z²`. -/
theorem aeval_deriv_mul_derivative_weierstrassSeries {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    aeval (weierstrassSeries hf hdeg hω hu) f.derivative
        * PowerSeries.derivative (weierstrassSeries hf hdeg hω hu)
      = 2 * PowerSeries.X := by
  have hc := Derivation.comp_aeval_eq (PowerSeries.derivative) f
    (a := weierstrassSeries hf hdeg hω hu)
  rw [weierstrassSeries_eval, smul_eq_mul] at hc
  rw [← hc, PowerSeries.derivative_pow, PowerSeries.derivative_X]
  simp

/-- The expansion of `ω = h(x) dx/y` on the Weierstrass disk at `(ω_bar, 0)`: the power series
`w_D(z) = 2·h(x(z))·f'(x(z))⁻¹`, where `x(z)` is the coordinate series (`z = y`). Pole-free
because `f'(x(z))` is a unit (`(H1)`, `p` odd). -/
noncomputable def omegaExpansionWeierstrass (h : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    O⟦X⟧ :=
  2 * aeval (weierstrassSeries hf hdeg hω hu) h
    * Ring.inverse (aeval (weierstrassSeries hf hdeg hω hu) f.derivative)

/-- Pole-free form: `f'(x(z)) · w_D(z) = 2·h(x(z))`. -/
theorem aeval_deriv_mul_omegaExpansionWeierstrass (h : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    aeval (weierstrassSeries hf hdeg hω hu) f.derivative * omegaExpansionWeierstrass h hf hdeg hω hu
      = 2 * aeval (weierstrassSeries hf hdeg hω hu) h := by
  rw [omegaExpansionWeierstrass]
  have huc := Ring.mul_inverse_cancel _ (isUnit_aeval_deriv_weierstrassSeries hf hdeg hω hu)
  linear_combination 2 * aeval (weierstrassSeries hf hdeg hω hu) h * huc

/-- Differential form: `z · w_D(z) = h(x(z)) · x'(z)`, i.e. `w_D dz = h(x) dx/y` with `y = z`
and `dx = x'(z) dz` (from the chain rule `f'(x)·x' = 2z`). -/
theorem X_mul_omegaExpansionWeierstrass (h : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    PowerSeries.X * omegaExpansionWeierstrass h hf hdeg hω hu
      = aeval (weierstrassSeries hf hdeg hω hu) h
        * PowerSeries.derivative (weierstrassSeries hf hdeg hω hu) := by
  rw [omegaExpansionWeierstrass]
  have hu' := isUnit_aeval_deriv_weierstrassSeries hf hdeg hω hu
  have hchain := aeval_deriv_mul_derivative_weierstrassSeries hf hdeg hω hu
  set u := aeval (weierstrassSeries hf hdeg hω hu) f.derivative
  set d := PowerSeries.derivative (weierstrassSeries hf hdeg hω hu)
  set ah := aeval (weierstrassSeries hf hdeg hω hu) h
  have huc : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu'
  linear_combination (-(ah * Ring.inverse u)) * hchain + (ah * d) * huc

/-! ### The formal antiderivative -/

variable {K : Type*} [Field K]

/-- The formal antiderivative of a power series over a field: `∑ (wₖ/(k + 1)) zᵏ⁺¹`
(so the constant coefficient is `0`). -/
noncomputable def antideriv (w : K⟦X⟧) : K⟦X⟧ :=
  mk fun n ↦ if n = 0 then 0 else coeff (n - 1) w / n

theorem coeff_antideriv (w : K⟦X⟧) (n : ℕ) :
    coeff n (antideriv w) = if n = 0 then 0 else coeff (n - 1) w / n :=
  coeff_mk _ _

@[simp] theorem coeff_succ_antideriv (w : K⟦X⟧) (n : ℕ) :
    coeff (n + 1) (antideriv w) = coeff n w / (n + 1) := by
  rw [coeff_antideriv]; simp

@[simp] theorem constantCoeff_antideriv (w : K⟦X⟧) : constantCoeff (antideriv w) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_antideriv, ite_eq_left rfl]

@[simp] theorem antideriv_add (v w : K⟦X⟧) :
    antideriv (v + w) = antideriv v + antideriv w := by
  refine PowerSeries.ext fun n ↦ ?_
  cases n <;> simp [coeff_antideriv, div_eq_mul_inv, add_mul]

@[simp] theorem antideriv_smul (c : K) (w : K⟦X⟧) : antideriv (c • w) = c • antideriv w := by
  refine PowerSeries.ext fun n ↦ ?_
  cases n <;> simp [coeff_antideriv, mul_div_assoc]

theorem antideriv_sum {ι : Type*} (s : Finset ι) (v : ι → K⟦X⟧) :
    antideriv (∑ i ∈ s, v i) = ∑ i ∈ s, antideriv (v i) := by
  refine PowerSeries.ext fun n ↦ ?_
  cases n <;> simp [coeff_antideriv, div_eq_mul_inv, Finset.sum_mul]

/-- The antiderivative of a linear combination — the shape in which the disk expansions of the
`ω′` basis enter the Coleman integral. -/
theorem antideriv_sum_smul {ι : Type*} (s : Finset ι) (c : ι → K) (v : ι → K⟦X⟧) :
    antideriv (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • antideriv (v i) := by
  rw [antideriv_sum]
  exact Finset.sum_congr rfl fun i _ ↦ antideriv_smul _ _

/-- The formal antiderivative is a right inverse of the formal derivative (fundamental
theorem of calculus for power series over a characteristic-zero field). -/
theorem derivative_antideriv [CharZero K] (w : K⟦X⟧) :
    PowerSeries.derivative (antideriv w) = w := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_succ_antideriv,
    div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)]

/-! ### The generic-disk antiderivative -/

variable [Algebra O K]

/-- The antiderivative `G^ω_D` of the generic-disk expansion of `ω = h(x) dx/y`, over the
fraction field: `G(z) = ∑ (w_D)ₖ/(k + 1) · zᵏ⁺¹` with `G(0) = 0`. -/
noncomputable def diskAntiderivGeneric (f h : O[X]) (a b : O) : K⟦X⟧ :=
  antideriv ((omegaExpansionGeneric f h a b).map (algebraMap O K))

@[simp] theorem constantCoeff_diskAntiderivGeneric (f h : O[X]) (a b : O) :
    constantCoeff (diskAntiderivGeneric (K := K) f h a b) = 0 :=
  constantCoeff_antideriv _

/-- The antiderivative `G^ω_D` of the Weierstrass-disk expansion of `ω = h(x) dx/y`, over the
fraction field, with `G(0) = 0`. -/
noncomputable def diskAntiderivWeierstrass (h : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    K⟦X⟧ :=
  antideriv ((omegaExpansionWeierstrass h hf hdeg hω hu).map (algebraMap O K))

@[simp] theorem constantCoeff_diskAntiderivWeierstrass (h : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    constantCoeff (diskAntiderivWeierstrass (K := K) h hf hdeg hω hu) = 0 :=
  constantCoeff_antideriv _

end ChabautyColeman
