/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Points of the hyperelliptic curve and the two charts

We model the points of the odd-degree hyperelliptic curve `y² = f(x)` over a field `K` by
`ChabautyColeman.CurvePoint K f`: either an affine point `(x, y)` on the curve, or the unique
point at infinity. The `x`- and `y`-coordinates and the infinity parameter `t = xᵍ/y` are
extracted by `xCoord`, `yCoord`, `tParam` (with junk value `0` at infinity).

Over the fraction field `K` of a discrete valuation ring `O`, with `f : O[X]` monic, the
**two charts** theorem `ChabautyColeman.point_int_or_inf` splits each affine point into *finite
type* (`x, y ∈ O`) and *infinite type* (`x, y ∉ O`, and then `t ∈ 𝔪`). Its analytic core is
`ChabautyColeman.valuation_eval_map_eq_pow`: at a point outside the valuation ring the leading
term of a monic polynomial dominates.

## Main definitions

* `ChabautyColeman.genus`: the genus `g` of `y² = f(x)`, i.e. `deg f / 2` (`deg f = 2g + 1`).
* `ChabautyColeman.CurvePoint`: the affine-plus-infinity point model of the curve.
* `ChabautyColeman.CurvePoint.tParam`: the infinity parameter `t = xᵍ/y`.

## Main statements

* `ChabautyColeman.genus_eq_of_natDegree_map`: the genus is read off from the degree of the
  image of `f` under any embedding of the base field.
* `ChabautyColeman.valuation_eval_map_eq_pow`: `𝓋 (f(x)) = 𝓋(x) ^ deg f` when `1 < 𝓋 x`.
* `ChabautyColeman.point_int_or_inf`: the two-charts dichotomy (`lem:two-charts`).
* `ChabautyColeman.CurvePoint.encard_univ`: there is exactly one point at infinity, so the
  points are the affine solutions of `y² = f(x)` plus one.

Blueprint node: `lem:two-charts`.
-/

@[expose] public section

open Polynomial IsDedekindDomain

namespace ChabautyColeman

/-- The genus of the odd-degree hyperelliptic curve `y² = f(x)`: `deg f = 2 * genus + 1`. -/
def genus {R : Type*} [Semiring R] (f : R[X]) : ℕ := f.natDegree / 2

theorem genus_eq {R : Type*} [Semiring R] (f : R[X]) : genus f = f.natDegree / 2 := rfl

theorem two_mul_genus_add_one {R : Type*} [Semiring R] {f : R[X]} (hf : Odd f.natDegree) :
    2 * genus f + 1 = f.natDegree := by
  obtain ⟨g, hg⟩ := hf; simp [genus, hg, Nat.mul_add_div]

theorem genus_eq_of_natDegree {R : Type*} [Semiring R] {f : R[X]} {n : ℕ}
    (h : f.natDegree = 2 * n + 1) : genus f = n := by
  rw [genus_eq, h]
  lia

/-- The genus is read off from the degree of the image of the defining polynomial under any
embedding of the base field: `deg f = 2g + 1`. -/
theorem genus_eq_of_natDegree_map {K L : Type*} [Field K] [Semiring L] [Nontrivial L]
    {p : K[X]} {n : ℕ} (φ : K →+* L) (h : (p.map φ).natDegree = 2 * n + 1) :
    genus p = n :=
  genus_eq_of_natDegree ((Polynomial.natDegree_map φ).symm.trans h)

@[simp] theorem genus_map {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S] {f : R[X]}
    (hf : f.Monic) (φ : R →+* S) : genus (f.map φ) = genus f := by
  simp only [genus, hf.natDegree_map]

/-- The genus `deg f / 2` of the polynomial-indexed development is the genus of an odd-degree
curve. -/
@[simp] theorem _root_.HyperellipticCurve.genus_f {R : Type*} [CommRing R] [Invertible (2 : R)]
    (C : HyperellipticCurve R) [C.IsOdd] : genus C.f = C.genus :=
  genus_eq_of_natDegree C.natDegree_f

/-- **The on-curve condition transports along a ring homomorphism**: the side condition of
`ChabautyColeman.CurvePoint.affine` for the image point. -/
theorem onCurve_map {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R[X]} {a b : R}
    (φ : R →+* S) (h : b ^ 2 = f.eval a) : φ b ^ 2 = (f.map φ).eval (φ a) := by
  rw [← map_pow, h, eval_map_apply]

/-- The on-curve condition at a Weierstrass point: the image of a root carries `y = 0`. -/
theorem onCurve_map_of_root {R S : Type*} [CommRing R] [CommRing S] {f : R[X]} {a : R}
    (φ : R →+* S) (h : f.eval a = 0) : (0 : S) ^ 2 = (f.map φ).eval (φ a) := by
  rw [zero_pow two_ne_zero, eval_map_apply, h, map_zero]

/-! ### The affine-plus-infinity point model -/

/-- A point of the odd-degree hyperelliptic curve `y² = f(x)` over a field `K`: either an
affine point `(x, y)` on the curve, or the unique point at infinity. -/
inductive CurvePoint (K : Type*) [Field K] (f : K[X]) where
  /-- The affine point `(x, y)` satisfying `y² = f(x)`. -/
  | affine (x y : K) (h : y ^ 2 = f.eval x)
  /-- The point at infinity. -/
  | infinity

namespace CurvePoint

variable {K : Type*} [Field K] {f : K[X]}

/-- The `x`-coordinate of an affine point; junk value `0` at infinity. -/
def xCoord : CurvePoint K f → K
  | affine x _ _ => x
  | infinity => 0

/-- The `y`-coordinate of an affine point; junk value `0` at infinity. -/
def yCoord : CurvePoint K f → K
  | affine _ y _ => y
  | infinity => 0

/-- The infinity parameter `t = xᵍ/y`; junk value `0` at infinity. -/
def tParam (P : CurvePoint K f) : K := P.xCoord ^ genus f / P.yCoord

@[simp] theorem xCoord_affine (x y : K) (h) : (affine x y h : CurvePoint K f).xCoord = x := rfl
@[simp] theorem yCoord_affine (x y : K) (h) : (affine x y h : CurvePoint K f).yCoord = y := rfl
@[simp] theorem xCoord_infinity : (infinity : CurvePoint K f).xCoord = 0 := rfl
@[simp] theorem yCoord_infinity : (infinity : CurvePoint K f).yCoord = 0 := rfl

@[simp] theorem tParam_affine (x y : K) (h) :
    (affine x y h : CurvePoint K f).tParam = x ^ genus f / y := rfl

@[simp] theorem tParam_infinity : (infinity : CurvePoint K f).tParam = 0 := by simp [tParam]

/-- A point is an affine solution of `y² = f(x)` or the point at infinity. This is the form
in which the points are counted: sums over the curve split off the term at infinity. -/
def equivOption : CurvePoint K f ≃ Option {p : K × K // p.2 ^ 2 = f.eval p.1} where
  toFun
    | affine x y h => some ⟨(x, y), h⟩
    | infinity => none
  invFun
    | some p => affine p.1.1 p.1.2 p.2
    | none => infinity
  left_inv := by rintro (⟨x, y, h⟩ | -) <;> rfl
  right_inv := by rintro (- | ⟨⟨x, y⟩, h⟩) <;> rfl

/-- An affine point is determined by its coordinate pair: the coordinate map is injective
away from the point at infinity. -/
theorem injOn_xCoord_yCoord :
    Set.InjOn (fun P : CurvePoint K f ↦ (P.xCoord, P.yCoord)) {P | P ≠ infinity} := by
  intro P hP Q hQ h
  cases P with
  | affine x y hxy =>
    cases Q with
    | affine x' y' hxy' =>
      simp only [Prod.mk.injEq, xCoord_affine, yCoord_affine] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | infinity => exact absurd rfl hQ
  | infinity => exact absurd rfl hP

/-- **The points of the curve are the affine solutions plus one**: in odd degree there is
exactly one point at infinity. This is what turns the projective count of blueprint
`thm:main-count` into its affine form. -/
theorem encard_univ (f : K[X]) :
    (Set.univ : Set (CurvePoint K f)).encard
      = {p : K × K | p.2 ^ 2 = f.eval p.1}.encard + 1 := by
  have hne : (infinity : CurvePoint K f) ∉ {P : CurvePoint K f | P ≠ infinity} := by simp
  have himg : (fun P : CurvePoint K f ↦ (P.xCoord, P.yCoord)) '' {P | P ≠ infinity}
      = {p : K × K | p.2 ^ 2 = f.eval p.1} := by
    ext ⟨x, y⟩
    refine ⟨fun ⟨P, hP, hxy⟩ ↦ ?_, fun h ↦ ⟨affine x y h, by simp, rfl⟩⟩
    cases P with
    | affine x' y' h' => rw [← hxy]; exact h'
    | infinity => exact absurd rfl hP
  rw [show (Set.univ : Set (CurvePoint K f)) = insert infinity {P | P ≠ infinity} by
      ext P; cases P <;> simp,
    Set.encard_insert_of_notMem hne, ← himg, injOn_xCoord_yCoord.encard_image]

instance instFinite [Finite K] : Finite (CurvePoint K f) := .of_equiv _ equivOption.symm

end CurvePoint

/-! ### Two charts over a discrete valuation ring -/

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- The `𝔪`-adic valuation on the fraction field `K` of the discrete valuation ring `O`. -/
local notation:max "𝓋" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal O)

/-- For a monic `f : O[X]` and `x : K` outside the valuation ring (`1 < 𝓋 x`), the leading
term dominates: `𝓋 (f(x)) = 𝓋(x) ^ deg f`. -/
theorem valuation_eval_map_eq_pow {f : O[X]} (hf : f.Monic) {x : K} (hx : 1 < 𝓋 x) :
    𝓋 ((f.map (algebraMap O K)).eval x) = 𝓋 x ^ f.natDegree := by
  set φ := algebraMap O K
  set g := f.map φ with hg
  have hgm : g.Monic := hf.map φ
  have hdeg : g.natDegree = f.natDegree := hf.natDegree_map φ
  have hdom : ∀ i ∈ Finset.range (g.natDegree + 1) \ {g.natDegree},
      𝓋 (g.coeff i * x ^ i) < 𝓋 (g.coeff g.natDegree * x ^ g.natDegree) := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
    have hilt : i < g.natDegree := by lia
    have hle : 𝓋 (g.coeff i) ≤ 1 := by
      rw [hg, coeff_map]
      exact (IsDiscreteValuationRing.maximalIdeal O).valuation_le_one _
    rw [map_mul, map_mul, map_pow, map_pow, hgm.coeff_natDegree, map_one, one_mul]
    calc 𝓋 (g.coeff i) * 𝓋 x ^ i ≤ 𝓋 x ^ i := mul_le_of_le_one_left' hle
      _ < 𝓋 x ^ g.natDegree := pow_lt_pow_right₀ hx hilt
  rw [← hdeg, eval_eq_sum_range,
    Valuation.map_sum_eq_of_lt _ (Finset.self_mem_range_succ g.natDegree) hdom,
    hgm.coeff_natDegree, one_mul, map_pow]

/-- **Two charts** (`lem:two-charts`). An affine point `(x, y)` of the odd-degree hyperelliptic
curve `y² = f(x)` over the fraction field `K` of a discrete valuation ring `O`, with `f : O[X]`
monic, is exactly one of: *finite type*, `x, y ∈ O` (`𝓋 x, 𝓋 y ≤ 1`); or *infinite type*,
`𝓋 x, 𝓋 y > 1` and the infinity parameter `t = xᵍ/y ∈ 𝔪` (`𝓋 t < 1`). The two cases are the
mutually exclusive alternatives `𝓋 x ≤ 1` and `1 < 𝓋 x`. -/
theorem point_int_or_inf {f : O[X]} (hf : f.Monic) [Fact (Odd f.natDegree)]
    {x y : K} (h : y ^ 2 = (f.map (algebraMap O K)).eval x) :
    (𝓋 x ≤ 1 ∧ 𝓋 y ≤ 1) ∨ (1 < 𝓋 x ∧ 1 < 𝓋 y ∧ 𝓋 (x ^ genus f / y) < 1) := by
  rcases le_or_gt (𝓋 x) 1 with hx | hx
  · refine .inl ⟨hx, ?_⟩
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    have hy2 : 𝓋 y ^ 2 ≤ 1 := by
      rw [← map_pow, h, eval_map_apply]
      exact (IsDiscreteValuationRing.maximalIdeal O).valuation_le_one _
    exact le_of_not_gt fun hy ↦ absurd hy2 (not_le.mpr (one_lt_pow₀ hy (by norm_num)))
  · have hval : 𝓋 y ^ 2 = 𝓋 x ^ f.natDegree := by
      rw [← map_pow, h, valuation_eval_map_eq_pow hf hx]
    have hpos : 1 < 𝓋 x ^ f.natDegree :=
      one_lt_pow₀ hx (by rw [← two_mul_genus_add_one (Fact.out : Odd f.natDegree)]; lia)
    have hy1 : 1 < 𝓋 y :=
      (one_lt_pow_iff_of_nonneg (n := 2) zero_le (by norm_num)).mp (by rw [hval]; exact hpos)
    refine .inr ⟨hx, hy1, ?_⟩
    have hXgY : 𝓋 x ^ genus f < 𝓋 y := by
      apply lt_of_pow_lt_pow_left₀ 2 zero_le
      rw [← pow_mul, hval, ← two_mul_genus_add_one (Fact.out : Odd f.natDegree)]
      exact pow_lt_pow_right₀ hx (by lia)
    rw [map_div₀, map_pow]
    exact (div_lt_one₀ (zero_lt_one.trans hy1)).mpr hXgY

end DVR

end ChabautyColeman

end
