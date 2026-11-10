/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.PointValuation
public import LeanPool.HyperellipticCurves.Disks.FuncExpansion

import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries

/-!
# Element-level order matching (generic chart), unconditional

The order of the generic-disk expansion of a function `P + Q·y`, taken over the coefficient
*field* `K` itself, equals the intrinsic order `emultiplicity (pointIdeal, (P + Q·y))` — with no
one-branch hypothesis (`ChabautyColeman.order_funcExpansionGeneric_eq_emultiplicity`).

The point: the function and its conjugate vanish *simultaneously* at `(a, b)` (with `b ≠ 0`)
exactly when `(x - a)` divides both `P` and `Q`. Splitting off `gcd P Q` — which multiplies both
the expansion (`funcExpansionGeneric_mul_left`) and the element
(`emultiplicity_pointIdeal_algebraMap_mul`) by matching amounts — reduces to the coprime case,
where at most one branch vanishes and the one-branch arguments
(`constantCoeff_funcExpansionGeneric`, the norm-conjugate trick, and
`emultiplicity_pointIdeal_element_generic`) apply.

Applied to the *reduced* data over the residue field (via
`ChabautyColeman.map_funcExpansionGeneric`), this identifies the order of the reduced disk
expansion with the intrinsic reduced order in the per-disk point sums of
`LeanPool.HyperellipticCurves.Specialization.DiskPointSum`, with no conjugate-nonvanishing
hypothesis — as
required for the reduction homomorphism `thm:redJ-hom`, where the generator of a principal divisor
cannot be chosen.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

/-! ### Common polynomial factors of expansions and elements -/

theorem funcExpansionGeneric_mul_left {O : Type*} [CommRing O] (f d P Q : O[X]) (a b : O) :
    funcExpansionGeneric f (d * P) (d * Q) a b
      = (taylor a d : O⟦X⟧) * funcExpansionGeneric f P Q a b := by
  rw [funcExpansionGeneric, funcExpansionGeneric, taylor_mul, taylor_mul, Polynomial.coe_mul,
    Polynomial.coe_mul]
  ring

theorem HypRing.algebraMap_mul_mk {R : Type*} [CommRing R] (f d P Q : R[X]) :
    (⟨d * P, d * Q⟩ : HypRing R f) = algebraMap R[X] (HypRing R f) d * ⟨P, Q⟩ := by
  ext <;> simp

section

variable {K : Type*} [Field K] {f : K[X]} [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)]

/-- Multiplying an element by a polynomial adds the polynomial's root multiplicity to the
intrinsic order (generic point). -/
theorem emultiplicity_pointIdeal_algebraMap_mul {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀)
    (hy : y₀ ≠ 0) {d : K[X]} (hd : d ≠ 0) (z : HypRing K f) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {algebraMap K[X] (HypRing K f) d * z})
      = rootMultiplicity x₀ d
        + emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {z}) := by
  have hP : Prime (pointIdeal f x₀ y₀) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ y₀) (pointIdeal_isPrime hb)
  rw [← Ideal.span_singleton_mul_span_singleton, emultiplicity_mul hP,
    emultiplicity_pointIdeal_generic hb hy hd]

/-! ### The unconditional element-level order match (generic chart) -/

/-- **Coprime polynomials cannot both vanish** at a common `a` witnessed via
`P(a) ± Q(a)·b = 0` with `b ≠ 0`: summing and differencing forces `P(a) = Q(a) = 0`, so
`X - a` divides both. -/
theorem isCoprime_not_both_eval_add {P Q : K[X]} {a b : K} (hcop : IsCoprime P Q) (hy : b ≠ 0)
    (h₁ : P.eval a + Q.eval a * b = 0) (h₂ : P.eval a - Q.eval a * b = 0) : False := by
  have hPa : P.eval a = 0 := by
    have h2P : 2 * P.eval a = 0 := by linear_combination h₁ + h₂
    exact (mul_eq_zero.mp h2P).resolve_left two_ne_zero
  have hQa : Q.eval a = 0 := by
    have h2Q : 2 * (Q.eval a * b) = 0 := by linear_combination h₁ - h₂
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h2Q).resolve_left two_ne_zero)).resolve_right hy
  exact Polynomial.not_isUnit_X_sub_C a
    (hcop.isUnit_of_dvd' (dvd_iff_isRoot.mpr hPa) (dvd_iff_isRoot.mpr hQa))

private theorem eval_conj_ne_zero_of_isCoprime {P Q : K[X]} {a b : K} (hy : b ≠ 0)
    (hcop : IsCoprime P Q) (hv : P.eval a + Q.eval a * b = 0) :
    P.eval a - Q.eval a * b ≠ 0 :=
  fun hc ↦ isCoprime_not_both_eval_add hcop hy hv hc

/-- Order match for a *coprime* pair: no common vanishing, so either the function or its
conjugate is nonzero at the point, and the one-branch arguments apply. -/
private theorem order_eq_emult_of_isCoprime {P Q : K[X]} {a b : K} (hb : b ^ 2 = f.eval a)
    (hy : b ≠ 0) (hN : P ^ 2 - f * Q ^ 2 ≠ 0) (hcop : IsCoprime P Q) :
    (funcExpansionGeneric f P Q a b).order
      = emultiplicity (pointIdeal f a b) (Ideal.span {(⟨P, Q⟩ : HypRing K f)}) := by
  have hfa : IsUnit (f.eval a) := isUnit_iff_ne_zero.mpr fun h0 ↦ pow_ne_zero 2 hy (hb.trans h0)
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  have hval : evalHom hb (⟨P, Q⟩ : HypRing K f) = P.eval a + Q.eval a * b :=
    evalHom_apply hb _
  have hstar : evalHom hb (star (⟨P, Q⟩ : HypRing K f)) = P.eval a - Q.eval a * b :=
    evalHom_star hb _
  rcases eq_or_ne (P.eval a + Q.eval a * b) 0 with hv | hv
  · -- the function vanishes at the point; coprimality forces the conjugate not to
    have hconj : P.eval a - Q.eval a * b ≠ 0 := eval_conj_ne_zero_of_isCoprime hy hcop hv
    have hordconj : (funcExpansionGeneric f P (-Q) a b).order = 0 := by
      refine PowerSeries.order_eq_zero_of_constantCoeff_ne_zero ?_
      rw [constantCoeff_funcExpansionGeneric, eval_neg]
      intro h
      exact hconj (by linear_combination h)
    have hordsum : (funcExpansionGeneric f P Q a b).order
        = ((P ^ 2 - f * Q ^ 2).rootMultiplicity a : ℕ∞) := by
      rw [← add_zero (funcExpansionGeneric f P Q a b).order, ← hordconj, ← order_mul,
        funcExpansionGeneric_mul_conj P Q hb hfa h2, PSeries.order_coe_taylor hN]
    have hE := emultiplicity_pointIdeal_element_generic (z := (⟨P, Q⟩ : HypRing K f)) hb hy
      hN (by rw [hstar]; exact hconj)
    rw [hordsum, hE]
  · -- the function does not vanish at the point: both sides are zero
    rw [PowerSeries.order_eq_zero_of_constantCoeff_ne_zero
        (by rw [constantCoeff_funcExpansionGeneric]; exact hv),
      emultiplicity_pointIdeal_element_eq_zero hb (by rw [hval]; exact hv)]

/-- **Order match for a function element, generic chart, unconditional.** The order of the
generic-disk expansion of `P + Q·y` (over the field `K` itself) equals the intrinsic order
`emultiplicity (pointIdeal, (P + Q·y))` — with no one-branch hypothesis: the common vanishing
of `P + Q·y` and its conjugate at `(a, b)` is exactly a common factor `(x - a)^m` of `P` and
`Q`, which is split off on both sides. -/
theorem order_funcExpansionGeneric_eq_emultiplicity (P Q : K[X]) {a b : K}
    (hb : b ^ 2 = f.eval a) (hy : b ≠ 0) (hN : P ^ 2 - f * Q ^ 2 ≠ 0) :
    (funcExpansionGeneric f P Q a b).order
      = emultiplicity (pointIdeal f a b) (Ideal.span {(⟨P, Q⟩ : HypRing K f)}) := by
  classical
  have hd0 : GCDMonoid.gcd P Q ≠ 0 := fun h0 ↦ hN <| by
    obtain ⟨hP, hQ⟩ := (gcd_eq_zero_iff P Q).mp h0
    rw [hP, hQ]; ring
  set d := GCDMonoid.gcd P Q
  have hPfac : d * (P / d) = P :=
    EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_left P Q)
  have hQfac : d * (Q / d) = Q :=
    EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_right P Q)
  have hcop : IsCoprime (P / d) (Q / d) := isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hd0
  have hN₀ : (P / d) ^ 2 - f * (Q / d) ^ 2 ≠ 0 := by
    intro h0
    refine hN ?_
    rw [← hPfac, ← hQfac]
    linear_combination (d ^ 2) * h0
  calc (funcExpansionGeneric f P Q a b).order
      = ((taylor a d : K⟦X⟧) * funcExpansionGeneric f (P / d) (Q / d) a b).order := by
        rw [← funcExpansionGeneric_mul_left, hPfac, hQfac]
    _ = (d.rootMultiplicity a : ℕ∞)
          + (funcExpansionGeneric f (P / d) (Q / d) a b).order := by
        rw [order_mul, PSeries.order_coe_taylor hd0]
    _ = (d.rootMultiplicity a : ℕ∞) + emultiplicity (pointIdeal f a b)
          (Ideal.span {(⟨P / d, Q / d⟩ : HypRing K f)}) := by
        rw [order_eq_emult_of_isCoprime hb hy hN₀ hcop]
    _ = emultiplicity (pointIdeal f a b) (Ideal.span {(⟨P, Q⟩ : HypRing K f)}) := by
        rw [← emultiplicity_pointIdeal_algebraMap_mul hb hy hd0, ← HypRing.algebraMap_mul_mk,
          hPfac, hQfac]

end

end ChabautyColeman
