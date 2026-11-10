/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Jacobian

/-!
# Curve points as height-one primes of the coordinate ring

A point `P = (x₀, y₀)` on `y² = f(x)` gives an evaluation ring homomorphism
`ChabautyColeman.evalHom : A_K → K`, `z ↦ z.re(x₀) + z.im(x₀)·y₀`, whose kernel is the point
ideal `ChabautyColeman.pointIdeal` (`pointIdeal_eq_ker`). Since it is surjective onto the field
`K`, the point ideal is maximal (`pointIdeal_isMaximal`), hence a height-one prime of the Dedekind
domain `A_K`: `ChabautyColeman.pointSpectrum`. This is the "point ↦ prime" map underlying the
intrinsic order `ord_P` of a function/differential at a residue point (`lem:ord-match`) and the
reduction of divisor classes (`def:redJ`).

## Main definitions

* `ChabautyColeman.evalHom`: evaluation of a coordinate-ring element at a curve point.
* `ChabautyColeman.pointSpectrum`: the height-one prime attached to a point.

## Main statements

* `ChabautyColeman.pointIdeal_eq_ker`: the point ideal is the kernel of `evalHom`.
* `ChabautyColeman.pointIdeal_isMaximal`: the point ideal is maximal.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {K : Type*} [Field K] {f : K[X]}

/-- Evaluation of a coordinate-ring element at a curve point `(x₀, y₀)` (with `y₀² = f(x₀)`):
`z ↦ z.re(x₀) + z.im(x₀)·y₀`. -/
noncomputable def evalHom {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) : HypRing K f →+* K where
  toFun z := z.re.eval x₀ + z.im.eval x₀ * y₀
  map_one' := by
    simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, eval_one, eval_zero, zero_mul,
      add_zero]
  map_zero' := by
    simp only [QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, eval_zero, zero_mul, add_zero]
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, eval_add]; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, eval_add, eval_mul, zero_mul,
      add_zero]
    linear_combination -(z.im.eval x₀ * w.im.eval x₀) * h

theorem evalHom_apply {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) (z : HypRing K f) :
    evalHom h z = z.re.eval x₀ + z.im.eval x₀ * y₀ := rfl

@[simp]
theorem evalHom_algebraMap {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) (p : K[X]) :
    evalHom h (algebraMap K[X] (HypRing K f) p) = p.eval x₀ := by
  simp [evalHom_apply]

@[simp]
theorem evalHom_y {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) : evalHom h (HypRing.y f) = y₀ := by
  simp [evalHom_apply, HypRing.y]

@[simp]
theorem evalHom_star {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) (z : HypRing K f) :
    evalHom h (star z) = z.re.eval x₀ - z.im.eval x₀ * y₀ := by
  rw [evalHom_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  simp only [zero_mul, add_zero, eval_neg]
  ring

theorem evalHom_surjective {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    Function.Surjective (evalHom h) :=
  fun k ↦ ⟨algebraMap K (HypRing K f) k, by simp [evalHom_apply]⟩

/-- The image of `p - C(p(x₀))` in `A_K` lies in the point ideal (it is divisible by `x - x₀`). -/
theorem algebraMap_sub_C_eval_mem (x₀ y₀ : K) (p : K[X]) :
    algebraMap K[X] (HypRing K f) (p - C (p.eval x₀)) ∈ pointIdeal f x₀ y₀ := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := x₀) (p := p)
  rw [hq, map_mul]
  exact Ideal.mul_mem_right _ _ (X_sub_C_mem_pointIdeal f x₀ y₀)

/-- The point ideal is exactly the kernel of the evaluation homomorphism. -/
theorem pointIdeal_eq_ker {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    pointIdeal f x₀ y₀ = RingHom.ker (evalHom h) := by
  refine le_antisymm ?_ ?_
  · rw [pointIdeal, Ideal.span_le]
    rintro g (rfl | rfl) <;>
      rw [SetLike.mem_coe, RingHom.mem_ker, evalHom_apply] <;>
      simp [HypRing.y]
  · intro z hz
    rw [RingHom.mem_ker, evalHom_apply] at hz
    have hmem (p : K[X]) : algebraMap K[X] (HypRing K f) p
        - algebraMap K (HypRing K f) (p.eval x₀) ∈ pointIdeal f x₀ y₀ := by
      have hC : algebraMap K (HypRing K f) (p.eval x₀)
          = algebraMap K[X] (HypRing K f) (C (p.eval x₀)) := by
        rw [IsScalarTower.algebraMap_apply K K[X] (HypRing K f), Polynomial.algebraMap_eq]
      rw [hC, ← map_sub]; exact algebraMap_sub_C_eval_mem x₀ y₀ p
    have hdecomp := HypRing.eq_algebraMap_re_add_im f z
    have hid : z = (algebraMap K[X] (HypRing K f) z.re - algebraMap K (HypRing K f) (z.re.eval x₀))
        + (algebraMap K[X] (HypRing K f) z.im - algebraMap K (HypRing K f) (z.im.eval x₀))
            * HypRing.y f
        + algebraMap K (HypRing K f) (z.im.eval x₀) * (HypRing.y f - algebraMap K _ y₀)
        + algebraMap K (HypRing K f) (z.re.eval x₀ + z.im.eval x₀ * y₀) := by
      nth_rw 1 [hdecomp]
      simp only [map_add, map_mul]; ring
    rw [hid, hz, map_zero, add_zero]
    exact add_mem (add_mem (hmem z.re) (Ideal.mul_mem_right _ _ (hmem z.im)))
      (Ideal.mul_mem_left _ _ (y_sub_mem_pointIdeal f x₀ y₀))

/-- A Mumford datum passing through the point: if `y - v` lies in the point ideal at
`(x₀, y₀)`, then `v` interpolates the `y`-coordinate there. -/
theorem eval_eq_of_y_sub_mem_pointIdeal {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) {v : K[X]}
    (hmem : HypRing.y f - algebraMap K[X] (HypRing K f) v ∈ pointIdeal f x₀ y₀) :
    v.eval x₀ = y₀ := by
  rw [pointIdeal_eq_ker h, RingHom.mem_ker, map_sub, evalHom_y, evalHom_algebraMap,
    sub_eq_zero] at hmem
  exact hmem.symm

/-- The point ideal of a curve point is maximal (its residue ring is `K`, via `evalHom`). -/
theorem pointIdeal_isMaximal {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    (pointIdeal f x₀ y₀).IsMaximal := by
  rw [pointIdeal_eq_ker h]
  exact RingHom.ker_isMaximal_of_surjective _ (evalHom_surjective h)

theorem pointIdeal_isPrime {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    (pointIdeal f x₀ y₀).IsPrime :=
  (pointIdeal_isMaximal h).isPrime

/-- The height-one prime of the Dedekind domain `A_K` corresponding to a curve point `(x₀, y₀)`. -/
noncomputable def pointSpectrum [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
    {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    IsDedekindDomain.HeightOneSpectrum (HypRing K f) where
  asIdeal := pointIdeal f x₀ y₀
  isPrime := pointIdeal_isPrime h
  ne_bot := pointIdeal_ne_bot f x₀ y₀

@[simp] theorem pointSpectrum_asIdeal [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] {x₀ y₀ : K} (h : y₀ ^ 2 = f.eval x₀) :
    (pointSpectrum h).asIdeal = pointIdeal f x₀ y₀ :=
  rfl

/-- The two point ideals over the same `x₀` with opposite `y₀` are distinct (for `y₀ ≠ 0`). -/
theorem pointIdeal_ne_neg {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) (hy : y₀ ≠ 0) (h2 : (2 : K) ≠ 0) :
    pointIdeal f x₀ y₀ ≠ pointIdeal f x₀ (-y₀) := by
  intro heq
  have hmem : HypRing.y f - algebraMap K (HypRing K f) (-y₀) ∈ pointIdeal f x₀ y₀ := by
    rw [heq]; exact y_sub_mem_pointIdeal f x₀ (-y₀)
  rw [pointIdeal_eq_ker hb, RingHom.mem_ker, map_sub] at hmem
  have hval : evalHom hb (HypRing.y f) - evalHom hb (algebraMap K (HypRing K f) (-y₀))
      = 2 * y₀ := by simp [evalHom_apply, HypRing.y]; ring
  rw [hval] at hmem
  exact mul_ne_zero h2 hy hmem

/-- The point ideal determines the curve point (only the left-hand point needs to lie on the
curve). -/
theorem pointIdeal_eq_pointIdeal_iff {x₀ y₀ x₁ y₁ : K} (h₀ : y₀ ^ 2 = f.eval x₀) :
    pointIdeal f x₀ y₀ = pointIdeal f x₁ y₁ ↔ x₀ = x₁ ∧ y₀ = y₁ := by
  refine ⟨fun heq ↦ ?_, fun ⟨hx, hy⟩ ↦ hx ▸ hy ▸ rfl⟩
  have hX : algebraMap K[X] (HypRing K f) (X - C x₁) ∈ pointIdeal f x₀ y₀ :=
    heq ▸ X_sub_C_mem_pointIdeal f x₁ y₁
  have hY : HypRing.y f - algebraMap K (HypRing K f) y₁ ∈ pointIdeal f x₀ y₀ :=
    heq ▸ y_sub_mem_pointIdeal f x₁ y₁
  rw [pointIdeal_eq_ker h₀, RingHom.mem_ker] at hX hY
  simp only [evalHom_algebraMap, map_sub, evalHom_y, IsScalarTower.algebraMap_apply K K[X],
    Polynomial.algebraMap_eq, eval_X, eval_C] at hX hY
  exact ⟨sub_eq_zero.mp hX, by linear_combination hY⟩

/-! ### The intrinsic order of a function at a point = root multiplicity -/

variable [NeZero (2 : K)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]

/-- A function nonvanishing at the point has multiplicity `0` there (`P = ker evalHom`). -/
theorem emultiplicity_pointIdeal_eq_zero {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) {g : K[X]}
    (hg : g.eval x₀ ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {algebraMap K[X] (HypRing K f) g}) = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  rw [Ideal.dvd_span_singleton, pointIdeal_eq_ker hb, RingHom.mem_ker,
    evalHom_algebraMap] at hdvd
  exact hg hdvd

/-- The multiplicity of a polynomial function `h` at a point ideal is `rootMultiplicity x₀ h` times
the multiplicity of `x - x₀` there (which is `1` at generic points, `2` at Weierstrass points). -/
theorem emultiplicity_pointIdeal_algebraMap {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) {h : K[X]}
    (hh : h ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {algebraMap K[X] (HypRing K f) h})
      = rootMultiplicity x₀ h • emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap K[X] (HypRing K f) (X - C x₀)}) := by
  have hP : Prime (pointIdeal f x₀ y₀) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ y₀) (pointIdeal_isPrime hb)
  set m := rootMultiplicity x₀ h
  set g := h /ₘ (X - C x₀) ^ m
  have hfac : (X - C x₀) ^ m * g = h := pow_mul_divByMonic_rootMultiplicity_eq h x₀
  have hgc : g.eval x₀ ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero x₀ hh
  have hspan : Ideal.span {algebraMap K[X] (HypRing K f) h}
      = Ideal.span {algebraMap K[X] (HypRing K f) (X - C x₀)} ^ m
        * Ideal.span {algebraMap K[X] (HypRing K f) g} := by
    rw [← hfac, map_mul, map_pow, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [hspan, emultiplicity_mul hP, emultiplicity_pow hP,
    emultiplicity_pointIdeal_eq_zero hb hgc, add_zero, nsmul_eq_mul]

/-- The generator `x - x₀` has multiplicity one at a generic point ideal (`y₀ ≠ 0`), since
`(x - x₀) = P · P'` with `P ≠ P'` the two point ideals above `x₀`. -/
theorem emultiplicity_pointIdeal_X_sub_C {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) (hy : y₀ ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀)
      (Ideal.span {algebraMap K[X] (HypRing K f) (X - C x₀)}) = 1 := by
  have hP : Prime (pointIdeal f x₀ y₀) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ y₀) (pointIdeal_isPrime hb)
  have hbneg : (-y₀) ^ 2 = f.eval x₀ := (neg_sq y₀).trans hb
  rw [← pointIdeal_mul_pointIdeal_neg f (Fact.out : Squarefree f) two_ne_zero hb,
    emultiplicity_mul hP,
    (FiniteMultiplicity.of_prime_left hP (pointIdeal_ne_bot f x₀ y₀)).emultiplicity_self]
  rw [emultiplicity_eq_zero.mpr (fun hdvd ↦ ?_), add_zero]
  rw [Ideal.dvd_iff_le] at hdvd
  exact pointIdeal_ne_neg hb hy two_ne_zero
    (((pointIdeal_isMaximal hbneg).eq_of_le (pointIdeal_isMaximal hb).ne_top hdvd).symm)

/-- At a Weierstrass point `(ω, 0)` the generator `x - ω` has multiplicity `2` (`(x - ω) = P²`,
since the two point ideals above `ω` coincide). -/
theorem emultiplicity_pointIdeal_X_sub_C_zero {x₀ : K} (hb : (0 : K) ^ 2 = f.eval x₀) :
    emultiplicity (pointIdeal f x₀ 0)
      (Ideal.span {algebraMap K[X] (HypRing K f) (X - C x₀)}) = 2 := by
  have hP : Prime (pointIdeal f x₀ 0) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ 0) (pointIdeal_isPrime hb)
  rw [← pointIdeal_mul_pointIdeal_neg f (Fact.out : Squarefree f) two_ne_zero hb, neg_zero,
    emultiplicity_mul hP,
    (FiniteMultiplicity.of_prime_left hP (pointIdeal_ne_bot f x₀ 0)).emultiplicity_self]
  rfl

/-- **Intrinsic order = root multiplicity (generic chart).** At a generic point `(x₀, y₀)`
(`y₀ ≠ 0`) the intrinsic order of a polynomial function `h` is `rootMultiplicity x₀ h`. -/
theorem emultiplicity_pointIdeal_generic {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) (hy : y₀ ≠ 0)
    {h : K[X]} (hh : h ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {algebraMap K[X] (HypRing K f) h})
      = rootMultiplicity x₀ h := by
  rw [emultiplicity_pointIdeal_algebraMap hb hh, emultiplicity_pointIdeal_X_sub_C hb hy]
  simp

/-- The intrinsic order (`emultiplicity`) of a coordinate-ring *element* `z` at a point ideal is
`0` iff `z` does not vanish at the point (`evalHom z ≠ 0`). -/
theorem emultiplicity_pointIdeal_element_eq_zero {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀)
    {z : HypRing K f} (hz : evalHom hb z ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {z}) = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  rw [Ideal.dvd_span_singleton, pointIdeal_eq_ker hb, RingHom.mem_ker] at hdvd
  exact hz hdvd

/-- **Intrinsic order of a function element (generic chart).** At a generic point `(x₀, y₀)`, if the
conjugate `star z` does not vanish there, the intrinsic order of `z = P + Q·y` equals the root
multiplicity of the norm polynomial `P² - f·Q²`. This is the algebraic counterpart of the analytic
norm decomposition of the disk-expansion order (`order_map_funcExpansionGeneric`). -/
theorem emultiplicity_pointIdeal_element_generic {x₀ y₀ : K} (hb : y₀ ^ 2 = f.eval x₀) (hy : y₀ ≠ 0)
    {z : HypRing K f} (hN : z.re ^ 2 - f * z.im ^ 2 ≠ 0) (hconj : evalHom hb (star z) ≠ 0) :
    emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {z})
      = rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) := by
  have hP : Prime (pointIdeal f x₀ y₀) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ y₀) (pointIdeal_isPrime hb)
  have h0 := emultiplicity_pointIdeal_element_eq_zero hb hconj
  have hkey : emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {z})
      + emultiplicity (pointIdeal f x₀ y₀) (Ideal.span {star z})
      = emultiplicity (pointIdeal f x₀ y₀)
          (Ideal.span {algebraMap K[X] (HypRing K f) (z.re ^ 2 - f * z.im ^ 2)}) := by
    rw [← emultiplicity_mul hP, Ideal.span_singleton_mul_span_singleton,
      HypRing.mul_star_eq_norm, HypRing.norm_eq]
  rwa [emultiplicity_pointIdeal_generic hb hy hN, h0, add_zero] at hkey

/-- **Intrinsic order = 2·root multiplicity (Weierstrass chart).** At a Weierstrass point `(ω, 0)`
the intrinsic order of a polynomial function `h` is `2·rootMultiplicity ω h`. -/
theorem emultiplicity_pointIdeal_weierstrass {x₀ : K} (hb : (0 : K) ^ 2 = f.eval x₀) {h : K[X]}
    (hh : h ≠ 0) :
    emultiplicity (pointIdeal f x₀ 0) (Ideal.span {algebraMap K[X] (HypRing K f) h})
      = rootMultiplicity x₀ h • (2 : ℕ∞) := by
  rw [emultiplicity_pointIdeal_algebraMap hb hh, emultiplicity_pointIdeal_X_sub_C_zero hb]

/-- **Intrinsic order of a function element (Weierstrass chart).** At a Weierstrass point `(x₀, 0)`
the intrinsic orders of `z` and its conjugate `star z` sum to `2·rootMult` of the norm polynomial
`z.re² - f·z.im²` (the analog of `emultiplicity_pointIdeal_element_generic`; here the conjugate
point coincides with the point, so the `2` from the double zero of `x - x₀` appears). -/
theorem emultiplicity_pointIdeal_element_weierstrass {x₀ : K} (hb : (0 : K) ^ 2 = f.eval x₀)
    {z : HypRing K f} (hN : z.re ^ 2 - f * z.im ^ 2 ≠ 0) :
    emultiplicity (pointIdeal f x₀ 0) (Ideal.span {z})
        + emultiplicity (pointIdeal f x₀ 0) (Ideal.span {star z})
      = rootMultiplicity x₀ (z.re ^ 2 - f * z.im ^ 2) • (2 : ℕ∞) := by
  have hP : Prime (pointIdeal f x₀ 0) :=
    Ideal.prime_of_isPrime (pointIdeal_ne_bot f x₀ 0) (pointIdeal_isPrime hb)
  rw [← emultiplicity_mul hP, Ideal.span_singleton_mul_span_singleton,
    HypRing.mul_star_eq_norm, HypRing.norm_eq, emultiplicity_pointIdeal_algebraMap hb hN,
    emultiplicity_pointIdeal_X_sub_C_zero hb]

end ChabautyColeman
