/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.CubeSlicing
public import LeanPool.CCDN.ArithmeticHeights.Duality
public import LeanPool.CCDN.ArithmeticHeights.MinkowskiSecond
public import LeanPool.CCDN.ArithmeticHeights.RationalLattice
public import LeanPool.CCDN.ArithmeticHeights.Siegel

/-!
# Bombieri–Vaaler's theorem over `ℤ`

For an `M × N` integer matrix `A` whose rows are linearly independent, the integral solutions of
`A x = 0` contain `N - M` linearly independent vectors `x₁, …, x_{N-M}` with

```text
∏ l, max n, |x l n|  ≤  D⁻¹ √(det (A Aᵀ)),
```

`D` the greatest common divisor of the maximal minors of `A`, and in particular a nonzero integral
solution with `max n, |x n| ≤ (D⁻¹ √(det (A Aᵀ)))^{1/(N-M)}`. These are Theorems 2 and 1 of
Bombieri–Vaaler 1983, and the right-hand side is an absolute height on the Grassmannian, so — unlike
the bound of Layer 5.1 — it does not move under `A ↦ U A` for `U ∈ GL_M(ℤ)`.

The proof is the assembly the roadmap prices it at: the covolume identity of Layer 4.3 over `ℚ`
identifies the covolume of the solution lattice with the Arakelov height of the solution space,
Layer 3.5 identifies that with the Arakelov height of the row space and Layer 3.4 computes the
latter as `D⁻¹ √(det (A Aᵀ))`, while Minkowski's second theorem (Layer 4.2) against the central
slice of the unit cube, whose volume Layer 4.5 bounds below by `2^{N-M}`, bounds the product of the
successive minima by that covolume. Layer 4.1 then supplies vectors realizing the minima.

## Main definitions

* `Submodule.cubeSlice`: the central slice `{y ∈ V | ∀ i, |y i| ≤ 1}` of the unit cube of
  `EuclideanSpace ℝ ι` by a subspace `V`. This is the convex body Minkowski's second theorem is
  applied to, and the body Layer 4.5 measures.
* `Int.Matrix.minorGcd`: the greatest common divisor of the maximal minors of an integer matrix,
  the `D` of Bombieri–Vaaler. The minors are Layer 3.1's Plücker coordinates of the rows.

## Main results

* `Int.Matrix.exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le`: **Bombieri–Vaaler's
  Theorem 2**, a small basis of the integral solutions.
* `Int.Matrix.exists_linearIndependent_mulVec_eq_zero_prod_mulHeight_le`: the same, with the
  multiplicative height of Layer 1 on the left — the `K = ℚ` case of the statement Layer 5.4 makes
  over a number field.
* `Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow`: **Bombieri–Vaaler's Theorem 1**,
  a single small nonzero integral solution.
* `Int.Matrix.sqrt_det_div_minorGcd_unit_mul`: **the invariance** of the bound under
  `A ↦ U A` for `U ∈ GL_M(ℤ)`, which is what Theorem 1 has over Layer 5.1's Siegel lemma.
* `Int.Matrix.minorGcd_mul_arakelovMulHeight_ker`: the identity the bound *is*,
  `D · H_Ar(ker A) = √(det (A Aᵀ))`.
* `ZLattice.prod_successiveMinimum_cubeSlice_le_covolume`: Minkowski's second theorem against the
  cube slice, with the factor `2^n` cancelled by Vaaler's bound. This is the geometric half of the
  theorem, and it knows no arithmetic.
* `NumberField.gcd_mul_arakelovMulHeight_intCast`: the Arakelov analogue of Layer 5.1's
  `Rat.gcd_mul_mulHeight_intCast`, the translation the arithmetic half is read through.
* `Int.Matrix.linearIndependent_row_map_rat_iff`, `Int.Matrix.det_pos`,
  `Int.Matrix.one_le_minorGcd`: the hypothesis and the two positivity facts that make the bound
  meaningful.

## Implementation notes

⚠ **The absolute value in Bombieri–Vaaler's `√|det (A Aᵀ)|` is redundant.** The Gram determinant of
the rows is a sum of squares of minors — this is Layer 3.4's `Matrix.det_mul_transpose_self_nonneg`
— and under the rank hypothesis it is *positive*, `Int.Matrix.det_pos`. The statements here carry
no absolute value, and the hypothesis is stated as `Int.Matrix.linearIndependent_row_map_rat_iff`
makes available: linear independence of the rows over `ℚ` is exactly `(A * Aᵀ).det ≠ 0`, a
condition on the integer matrix alone.

⚠ **The milestone needs Layer 3.5, which its pricing does not mention.** The roadmap prices 5.2 at
"3.4, 4.2, 4.5 and the `ℚ`-case of 4.3", and Layer 4.3 delivers the covolume of the solution
lattice as the Arakelov height of the *solution space*. Turning that into the minors of `A` is the
duality theorem `Matrix.arakelovMulHeight_ker_mulVecLin` of Layer 3.5, and nothing else will do:
the Plücker coordinates of the kernel are the complementary minors, which is what duality says.
So the `ℚ` spine is 3.1 → 3.2 → 3.3 → 3.4, 3.5 → 4.1 → 4.2 → 4.3(`ℚ`) → 4.5 → 5.2, one rung longer
than advertised, and every rung of it is landed.

⚠ **The `2^n` of Minkowski's second theorem and the `2^n` of Vaaler's cube-slicing theorem cancel
exactly, and that is the whole of why the constant is `1`.** Layer 4.2 bounds
`(∏ λ i) · vol B` by `2^n · covol L`, and Layer 4.5 bounds `vol B` below by `2^n` for `B` the cube
slice; the product of the minima is therefore at most the covolume, with no constant at all. Any
body with a worse slice bound would leave a constant behind, which is precisely what happens over a
number field with a complex place — Layer 5.4's `(2/π)^{k r₂ / d}`.

⚠ **The basis form needs no hypothesis `M < N`.**
`Int.Matrix.exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le` is stated for `Fin (N - M)`
solutions and is sharp at `N = M`, where both sides are `1`: the empty
product on the left, and on the right the Arakelov height of the zero subspace. Only the one-vector
form needs `M < N`, and there it is not removable — the exponent `1/(N - M)` requires it.

⚠ **The left-hand side is the sup norm, and the height form is strictly weaker.** By Layer 5.1's
`Rat.gcd_mul_mulHeight_intCast` the height of an integer tuple is its sup norm divided by the
content, so `∏ H(x l) ≤ ∏ max |x l n|` with equality exactly when every `x l` is primitive. The
basis produced here is *not* primitive in general — the minima vectors of a lattice need not be —
so the height form recorded as
`Int.Matrix.exists_linearIndependent_mulVec_eq_zero_prod_mulHeight_le` is a genuine weakening, and
it is the form Layer 5.4 generalizes.

## References

E. Bombieri and J. Vaaler, "On Siegel's lemma", *Inventiones Mathematicae* **73** (1983), 11–32,
Theorems 1 and 2, and equation (2.5) for the invariance.

I. Aliev and M. Henk, "Successive minima and best simultaneous Diophantine approximations",
*Monatshefte für Mathematik* **147** (2006), 95–101, §6, Theorems 6.2–6.3, where this assembly is
written out adele-free and the `ℚ` case of the covolume identity is quoted as folklore.

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem 2.9.4 and Remark 2.9.5 for the number-field statement this is the `K = ℚ` case of.

This is Layer 5.2 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset MeasureTheory Module Submodule Matrix exteriorPower
open scoped ENNReal Pointwise

/-!
### The central slice of the unit cube

The convex body Minkowski's second theorem is applied to. Everything in this section is elementary;
the one statement with content about it is Layer 4.5's `two_pow_finrank_le_volume_inter_cube`, which
bounds its volume below by `2 ^ dim V`.
-/

namespace Submodule

variable {ι : Type*} (V : Submodule ℝ (EuclideanSpace ℝ ι))

/-- The **central slice of the unit cube** `[-1, 1]^ι` by a subspace `V` of `EuclideanSpace ℝ ι`,
as a subset of `V`. -/
def cubeSlice : Set ↥V := {y : ↥V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1}

theorem mem_cubeSlice {y : ↥V} : y ∈ V.cubeSlice ↔ ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1 :=
  Iff.rfl

/-- A dilation of the cube slice is the slice of the corresponding cube, which is how a bound by a
successive minimum is read off. -/
theorem mem_smul_cubeSlice {r : ℝ} (hr : 0 < r) {y : ↥V} :
    y ∈ r • V.cubeSlice ↔ ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ r := by
  have h : r • V.cubeSlice = {y : ↥V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ r} := by
    rw [show V.cubeSlice = {y : ↥V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1} from rfl,
      smul_setOf_abs_le V hr, mul_one]
  rw [h]
  exact Iff.rfl

theorem convex_cubeSlice : Convex ℝ V.cubeSlice := by
  intro x hx y hy a b ha hb hab i
  have h : ((a • x + b • y : ↥V) : EuclideanSpace ℝ ι) i
      = a * (x : EuclideanSpace ℝ ι) i + b * (y : EuclideanSpace ℝ ι) i := by
    simp
  rw [h]
  calc |a * (x : EuclideanSpace ℝ ι) i + b * (y : EuclideanSpace ℝ ι) i|
      ≤ |a * (x : EuclideanSpace ℝ ι) i| + |b * (y : EuclideanSpace ℝ ι) i| := abs_add_le _ _
    _ = a * |(x : EuclideanSpace ℝ ι) i| + b * |(y : EuclideanSpace ℝ ι) i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr; exacts [hx i, hy i]
    _ = 1 := by rw [mul_one, mul_one, hab]

theorem neg_mem_cubeSlice {x : ↥V} (hx : x ∈ V.cubeSlice) : -x ∈ V.cubeSlice := by
  intro i
  have h : ((-x : ↥V) : EuclideanSpace ℝ ι) i = -(x : EuclideanSpace ℝ ι) i := by simp
  rw [h, abs_neg]
  exact hx i

theorem isClosed_cubeSlice : IsClosed V.cubeSlice := by
  have h : V.cubeSlice = ⋂ i, (fun y : ↥V ↦ (y : EuclideanSpace ℝ ι) i) ⁻¹' (Set.Icc (-1) 1) := by
    ext y
    simp [cubeSlice, abs_le, Set.mem_Icc]
  rw [h]
  refine isClosed_iInter fun i ↦ IsClosed.preimage ?_ isClosed_Icc
  fun_prop

theorem isBounded_cubeSlice [Finite ι] : Bornology.IsBounded V.cubeSlice := by
  have : Fintype ι := Fintype.ofFinite ι
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : ↥V)) (r := Real.sqrt (Fintype.card ι))) ?_
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖y‖ = ‖(y : EuclideanSpace ℝ ι)‖ := rfl
  rw [hnorm, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖(y : EuclideanSpace ℝ ι) i‖ ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg ((y : EuclideanSpace ℝ ι) i), hy i]
    _ = (Fintype.card ι : ℝ) := by simp

theorem interior_cubeSlice_nonempty [Finite ι] : (interior V.cubeSlice).Nonempty := by
  set U : Set ↥V := ⋂ i, (fun y : ↥V ↦ (y : EuclideanSpace ℝ ι) i) ⁻¹' (Set.Ioo (-1) 1) with hU
  have hsub : U ⊆ V.cubeSlice := by
    intro y hy i
    rw [hU] at hy
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo] at hy
    exact abs_le.2 ⟨(hy i).1.le, (hy i).2.le⟩
  have hopen : IsOpen U := by
    rw [hU]
    refine isOpen_iInter_of_finite fun i ↦ IsOpen.preimage ?_ isOpen_Ioo
    fun_prop
  have hmem : (0 : ↥V) ∈ U := by rw [hU]; simp
  exact ⟨0, interior_maximal hsub hopen hmem⟩

end Submodule

/-!
### Minkowski's second theorem against the cube slice

Layers 4.2 and 4.5, combined: the two factors `2 ^ n` cancel and the product of the successive
minima is bounded by the covolume with no constant.
-/

namespace ZLattice

variable {ι : Type*} [Fintype ι] (V : Submodule ℝ (EuclideanSpace ℝ ι))

/-- **The geometric half of Bombieri–Vaaler's theorem.** For the central slice of the unit cube as
the convex body, the product of the successive minima of a lattice in a subspace of
`EuclideanSpace ℝ ι` is at most the covolume of the lattice. The `2 ^ n` of Minkowski's second
theorem (Layer 4.2) is cancelled exactly by Vaaler's slice bound (Layer 4.5). -/
theorem prod_successiveMinimum_cubeSlice_le_covolume (L : Submodule ℤ ↥V) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    ∏ i ∈ Finset.range (finrank ℝ ↥V), successiveMinimum L V.cubeSlice i ≤ covolume L := by
  have hM := prod_successiveMinimum_mul_measure_le L volume V.convex_cubeSlice
    (fun _ hx ↦ V.neg_mem_cubeSlice hx) V.interior_cubeSlice_nonempty V.isBounded_cubeSlice
  have hvol : (2 : ℝ≥0∞) ^ finrank ℝ ↥V ≤ volume V.cubeSlice :=
    two_pow_finrank_le_volume_inter_cube V
  have hfin : volume V.cubeSlice ≠ ⊤ := (V.isBounded_cubeSlice.measure_lt_top).ne
  have hvolr : (2 : ℝ) ^ finrank ℝ ↥V ≤ (volume V.cubeSlice).toReal := by
    rw [show ((2 : ℝ) ^ finrank ℝ ↥V) = ((2 : ℝ≥0∞) ^ finrank ℝ ↥V).toReal by
      rw [ENNReal.toReal_pow]; norm_num]
    exact ENNReal.toReal_mono hfin hvol
  have hppos : 0 < ∏ i ∈ Finset.range (finrank ℝ ↥V), successiveMinimum L V.cubeSlice i :=
    Finset.prod_pos fun i hi ↦ successiveMinimum_pos L V.convex_cubeSlice
      (fun _ hx ↦ V.neg_mem_cubeSlice hx) V.interior_cubeSlice_nonempty V.isBounded_cubeSlice
      (Finset.mem_range.1 hi)
  have h2pos : (0 : ℝ) < 2 ^ finrank ℝ ↥V := by positivity
  nlinarith [hM, hvolr, hppos, h2pos]

end ZLattice

/-!
### The Arakelov height of an integer tuple

The Arakelov analogue of Layer 5.1's `Rat.gcd_mul_mulHeight_intCast`, which is what turns the
Plücker point of the row space into a euclidean norm of minors.
-/

namespace NumberField

/-- **The Arakelov sup-norm-to-height translation.** The Arakelov height of a nonzero tuple of
integers, read as a tuple of rationals, is its euclidean norm divided by the greatest common
divisor of its entries. Layer 4.3's `NumberField.arakelovMulHeight_intCast_of_gcd_eq_one` is the
primitive case, and Layer 5.1's `Rat.gcd_mul_mulHeight_intCast` is the same statement for the sup
norm. -/
theorem gcd_mul_arakelovMulHeight_intCast {κ : Type*} [Fintype κ] {x : κ → ℤ} (hx : x ≠ 0) :
    ((univ.gcd x : ℤ) : ℝ) * arakelovMulHeight (((↑) : ℤ → ℚ) ∘ x) =
      Real.sqrt (∑ i, ((x i : ℝ)) ^ 2) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hg0 : univ.gcd x ≠ 0 := fun h ↦ hi₀ (Finset.gcd_eq_zero_iff.1 h i₀ (mem_univ i₀))
  have hgnn : 0 ≤ univ.gcd x := by
    rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]
    exact abs_nonneg _
  have hdvd : ∀ i, univ.gcd x ∣ x i := fun i ↦ Finset.gcd_dvd (mem_univ i)
  set y : κ → ℤ := fun i ↦ x i / univ.gcd x with hy
  have hxy : ∀ i, x i = univ.gcd x * y i := fun i ↦ (Int.mul_ediv_cancel' (hdvd i)).symm
  have hy1 : univ.gcd y = 1 := Finset.gcd_div_eq_one (mem_univ i₀) hi₀
  have hsmul : (((↑) : ℤ → ℚ) ∘ x) = ((univ.gcd x : ℤ) : ℚ) • (((↑) : ℤ → ℚ) ∘ y) := by
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (hxy i)
  rw [hsmul, arakelovMulHeight_smul_eq _ (by exact_mod_cast hg0),
    arakelovMulHeight_intCast_of_gcd_eq_one hy1,
    show ((univ.gcd x : ℤ) : ℝ) = Real.sqrt (((univ.gcd x : ℤ) : ℝ) ^ 2) by
      rw [Real.sqrt_sq (by exact_mod_cast hgnn)], ← Real.sqrt_mul (by positivity), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← mul_pow]
  norm_cast
  rw [← hxy i]

end NumberField

/-!
### The greatest common divisor of the maximal minors
-/

namespace Int.Matrix

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The **greatest common divisor of the maximal minors** of an integer matrix — the `D` of
Bombieri–Vaaler. The minors are Layer 3.1's Plücker coordinates of the rows, indexed by the sets of
`m` columns. -/
noncomputable def minorGcd (A : _root_.Matrix (Fin m) ι ℤ) : ℤ :=
  (univ : Finset (Set.powersetCard ι m)).gcd (plucker m A.row)

/-- The minors of the rational matrix are the minors of the integer matrix, cast. -/
private theorem plucker_row_map_rat (A : _root_.Matrix (Fin m) ι ℤ) :
    plucker m (A.map ((↑) : ℤ → ℚ)).row = ((↑) : ℤ → ℚ) ∘ plucker m A.row :=
  funext fun s ↦ plucker_row_map (Int.castRingHom ℚ) A s

/-- Under the rank hypothesis some maximal minor is nonzero. -/
private theorem plucker_row_ne_zero {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : plucker m A.row ≠ 0 := by
  intro h
  refine (linearIndependent_row_iff_plucker_row_ne_zero (A.map ((↑) : ℤ → ℚ))).1 hA ?_
  rw [plucker_row_map_rat, h]
  rfl

/-- **The rank hypothesis is a condition on the integer matrix alone**: the rows are linearly
independent over `ℚ` exactly when the Gram determinant of the rows is nonzero. This is Layer 3.4's
Gram criterion, read over `ℤ`. -/
theorem linearIndependent_row_map_rat_iff (A : _root_.Matrix (Fin m) ι ℤ) :
    LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row ↔ (A * Aᵀ).det ≠ 0 := by
  have hmap : (A.map ((↑) : ℤ → ℚ)) * (A.map ((↑) : ℤ → ℚ))ᵀ = (A * Aᵀ).map ((↑) : ℤ → ℚ) := by
    ext i j
    simp only [_root_.Matrix.mul_apply, _root_.Matrix.map_apply, _root_.Matrix.transpose_apply]
    push_cast
    rfl
  have hdet : ((A * Aᵀ).map ((↑) : ℤ → ℚ)).det = ((A * Aᵀ).det : ℚ) :=
    (RingHom.map_det (Int.castRingHom ℚ) (A * Aᵀ)).symm
  rw [linearIndependent_row_iff_det_mul_transpose_self_ne_zero, hmap, hdet, ne_eq, ne_eq,
    Int.cast_eq_zero]

/-- **The Gram determinant is positive** under the rank hypothesis, so the Bombieri–Vaaler bound is
a positive real and the absolute value the literature writes around `det (A Aᵀ)` is redundant. -/
theorem det_pos {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 0 < (A * Aᵀ).det := by
  rw [_root_.Matrix.det_mul_transpose_self_eq_sum_sq]
  obtain ⟨s, hs⟩ := Function.ne_iff.1 (plucker_row_ne_zero hA)
  refine Finset.sum_pos' (fun t _ ↦ sq_nonneg _) ⟨s, mem_univ s, ?_⟩
  have hs' : plucker m A.row s ≠ 0 := by simpa using hs
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs'))

/-- The divisor `D` is at least `1` under the rank hypothesis: it is a normalized greatest common
divisor of integers not all zero. -/
theorem one_le_minorGcd {A : _root_.Matrix (Fin m) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) : 1 ≤ minorGcd A := by
  have hD0 : minorGcd A ≠ 0 := fun h ↦ plucker_row_ne_zero hA
    (funext fun s ↦ Finset.gcd_eq_zero_iff.1 h s (mem_univ s))
  have hDnn : 0 ≤ minorGcd A := by
    rw [minorGcd, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]
    exact abs_nonneg _
  omega

/-- **The identity the Bombieri–Vaaler bound is**: `D` times the Arakelov height of the solution
space of `A x = 0` is `√(det (A Aᵀ))`. Layer 3.5 identifies the height of the solution space with
that of the row space, Layer 3.3 computes the latter as the height of the tuple of maximal minors,
and `NumberField.gcd_mul_arakelovMulHeight_intCast` divides out its content; the sum of squares of
minors is Layer 3.4's Cauchy–Binet identity. -/
theorem minorGcd_mul_arakelovMulHeight_ker (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ((minorGcd A : ℤ) : ℝ) *
        (LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin).arakelovMulHeight
      = Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) := by
  have hp := plucker_row_map_rat A
  have hne := plucker_row_ne_zero hA
  rw [_root_.Matrix.arakelovMulHeight_ker_mulVecLin, Submodule.arakelovMulHeight_span_range hA, hp,
    minorGcd, NumberField.gcd_mul_arakelovMulHeight_intCast hne,
    _root_.Matrix.det_mul_transpose_self_eq_sum_sq]
  push_cast
  rfl

/-- A row operation of determinant `±1` does not change the divisor `D`: it scales every maximal
minor by that determinant, which a normalized greatest common divisor does not see. -/
theorem minorGcd_unit_mul {U : _root_.Matrix (Fin m) (Fin m) ℤ} (hU : IsUnit U.det)
    (A : _root_.Matrix (Fin m) ι ℤ) : minorGcd (U * A) = minorGcd A := by
  have hnorm : normalize U.det = 1 := normalize_eq_one.2 hU
  rw [minorGcd, minorGcd, plucker_row_mul,
    show (U.det • plucker m A.row) = (fun s ↦ U.det * plucker m A.row s) from rfl,
    Finset.gcd_mul_left, hnorm, one_mul]

/-- A row operation of determinant `±1` does not change the Gram determinant of the rows. -/
theorem det_mul_transpose_self_unit_mul {U : _root_.Matrix (Fin m) (Fin m) ℤ} (hU : IsUnit U.det)
    (A : _root_.Matrix (Fin m) ι ℤ) : ((U * A) * (U * A)ᵀ).det = (A * Aᵀ).det := by
  have hsq : U.det ^ 2 = 1 := by rcases Int.isUnit_iff.1 hU with h | h <;> rw [h] <;> norm_num
  rw [_root_.Matrix.det_mul_transpose_self_eq_sum_sq,
    _root_.Matrix.det_mul_transpose_self_eq_sum_sq, plucker_row_mul]
  calc ∑ s : Set.powersetCard ι m, (U.det • plucker m A.row) s ^ 2
      = ∑ s : Set.powersetCard ι m, U.det ^ 2 * plucker m A.row s ^ 2 :=
        Finset.sum_congr rfl fun s _ ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    _ = ∑ s : Set.powersetCard ι m, plucker m A.row s ^ 2 := by rw [hsq]; simp only [one_mul]

/-- **The invariance of the Bombieri–Vaaler bound** (Bombieri–Vaaler (2.5)): `D⁻¹ √(det (A Aᵀ))` is
unchanged by `A ↦ U A` for `U ∈ GL_M(ℤ)`, which fixes the solution space. This is what Theorem 1
has over the classical Siegel lemma of Layer 5.1, whose bound depends on the entries and so moves
under a row operation. -/
theorem sqrt_det_div_minorGcd_unit_mul {U : _root_.Matrix (Fin m) (Fin m) ℤ} (hU : IsUnit U.det)
    (A : _root_.Matrix (Fin m) ι ℤ) :
    Real.sqrt ((((U * A) * (U * A)ᵀ).det : ℤ) : ℝ) / ((minorGcd (U * A) : ℤ) : ℝ)
      = Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ) := by
  rw [det_mul_transpose_self_unit_mul hU, minorGcd_unit_mul hU]

/-!
### Bombieri–Vaaler's theorems
-/

omit [LinearOrder ι] in
/-- The solution space of `A x = 0` has dimension `N - M` when the rows are independent. -/
private theorem finrank_ker (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    finrank ℚ ↥(LinearMap.ker (A.map ((↑) : ℤ → ℚ)).mulVecLin) = Fintype.card ι - m := by
  have hrank : (A.map ((↑) : ℤ → ℚ)).rank = m := by
    simpa using hA.rank_matrix
  have h := LinearMap.finrank_range_add_finrank_ker (A.map ((↑) : ℤ → ℚ)).mulVecLin
  rw [show finrank ℚ ↥(LinearMap.range (A.map ((↑) : ℤ → ℚ)).mulVecLin)
      = (A.map ((↑) : ℤ → ℚ)).rank from rfl, hrank] at h
  simp only [Module.finrank_pi] at h
  omega

/-- **Bombieri–Vaaler's Theorem 2** (Bombieri–Vaaler 1983, Theorem 2; Aliev–Henk §6, Theorem 6.3).
For an `M × N` integer matrix with linearly independent rows there are `N - M` linearly independent
integral solutions of `A x = 0` whose sup norms have product at most `D⁻¹ √(det (A Aᵀ))`, `D` the
greatest common divisor of the maximal minors.

No hypothesis `M < N` is needed: at `N = M` the conclusion is the empty product `1` on the left and
the Arakelov height of the zero subspace, also `1`, on the right. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ x : Fin (Fintype.card ι - m) → (ι → ℤ), LinearIndependent ℤ x ∧ (∀ l, A *ᵥ x l = 0) ∧
      (∏ l, ((⨆ i, |x l i| : ℤ) : ℝ)) ≤
        Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ) := by
  set Aq := A.map ((↑) : ℤ → ℚ) with hAqdef
  set V := LinearMap.ker Aq.mulVecLin with hVdef
  have hrs : finrank ℝ ↥V.realSpan = Fintype.card ι - m := by
    rw [Submodule.finrank_realSpan, hVdef, finrank_ker A hA]
  have hmink := ZLattice.prod_successiveMinimum_cubeSlice_le_covolume V.realSpan V.intLattice
  rw [Submodule.covolume_intLattice] at hmink
  obtain ⟨v, hvL, hvind, hvmem⟩ :=
    ZLattice.exists_linearIndependent_mem_smul_successiveMinimum V.intLattice
      V.realSpan.convex_cubeSlice (fun _ hx ↦ V.realSpan.neg_mem_cubeSlice hx)
      V.realSpan.interior_cubeSlice_nonempty V.realSpan.isBounded_cubeSlice
      V.realSpan.isClosed_cubeSlice
  choose z hzV hzc using fun j ↦ Submodule.mem_intLattice.1 (hvL j)
  have hzco : ∀ j i, ((z j i : ℤ) : ℝ) = (v j : EuclideanSpace ℝ ι) i := fun j i ↦ by
    rw [hzc j]; rfl
  rw [← hrs]
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc j
    have key : ∑ l, (c l : ℝ) • v l = 0 := by
      refine Submodule.coe_eq_zero.1 ?_
      ext i
      have hco : ((∑ l, (c l : ℝ) • v l : ↥V.realSpan) : EuclideanSpace ℝ ι) i
          = ∑ l, (c l : ℝ) * (v l : EuclideanSpace ℝ ι) i := by
        push_cast
        simp [Finset.sum_apply]
      rw [hco]
      have h2 : ∀ l, (c l : ℝ) * (v l : EuclideanSpace ℝ ι) i = ((c l * z l i : ℤ) : ℝ) :=
        fun l ↦ by rw [← hzco l i]; push_cast; ring
      rw [Finset.sum_congr rfl fun l _ ↦ h2 l, ← Int.cast_sum]
      have h3 : ∑ l, c l * z l i = 0 := by
        have := congrFun hc i
        simpa [Finset.sum_apply] using this
      rw [h3]
      simp
    exact_mod_cast Fintype.linearIndependent_iff.1 hvind (fun l ↦ (c l : ℝ)) key j
  · intro l
    funext i
    have h : (Aq *ᵥ Rat.piIntCast ι (z l)) i = 0 := by
      have hk := LinearMap.mem_ker.1 (hzV l)
      rw [_root_.Matrix.mulVecLin_apply] at hk
      exact congrFun hk i
    have hcast : ((A *ᵥ z l) i : ℚ) = (Aq *ᵥ Rat.piIntCast ι (z l)) i := by
      simp only [_root_.Matrix.mulVec, dotProduct, hAqdef, _root_.Matrix.map_apply,
        Rat.piIntCast_apply]
      push_cast
      rfl
    have hz : ((A *ᵥ z l) i : ℚ) = 0 := by rw [hcast, h]
    exact_mod_cast hz
  · have hid : ((minorGcd A : ℤ) : ℝ) * V.arakelovMulHeight
        = Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) := minorGcd_mul_arakelovMulHeight_ker A hA
    have hD1 : (1 : ℝ) ≤ ((minorGcd A : ℤ) : ℝ) := by exact_mod_cast one_le_minorGcd hA
    have hDne : ((minorGcd A : ℤ) : ℝ) ≠ 0 := by linarith
    have hrhs : Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ)
        = V.arakelovMulHeight := by
      rw [← hid, mul_comm, mul_div_assoc, div_self hDne, mul_one]
    rw [hrhs]
    refine le_trans ?_ hmink
    rw [← Fin.prod_univ_eq_prod_range]
    have hbound : ∀ l : Fin (finrank ℝ ↥V.realSpan),
        0 ≤ (((⨆ i, |z l i| : ℤ)) : ℝ) ∧ (((⨆ i, |z l i| : ℤ)) : ℝ) ≤
          ZLattice.successiveMinimum V.intLattice V.realSpan.cubeSlice l := by
      intro l
      have hne : Nonempty ι := by
        have h1 : 0 < finrank ℝ ↥V.realSpan := lt_of_le_of_lt (Nat.zero_le _) l.isLt
        rw [hrs] at h1
        exact Fintype.card_pos_iff.1 (by omega)
      obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ |z l i|)
      have hval : (((⨆ i, |z l i| : ℤ)) : ℝ) = |(v l : EuclideanSpace ℝ ι) i₀| := by
        rw [← hi₀, Int.cast_abs, hzco l i₀]
      rw [hval]
      refine ⟨abs_nonneg _, (V.realSpan.mem_smul_cubeSlice ?_).1 (hvmem l) i₀⟩
      exact ZLattice.successiveMinimum_pos V.intLattice V.realSpan.convex_cubeSlice
        (fun _ hx ↦ V.realSpan.neg_mem_cubeSlice hx) V.realSpan.interior_cubeSlice_nonempty
        V.realSpan.isBounded_cubeSlice l.isLt
    exact Finset.prod_le_prod₀ (fun l _ ↦ (hbound l).1) fun l _ ↦ (hbound l).2

/-- **Bombieri–Vaaler's Theorem 2, in height form** — the `K = ℚ` case of the statement Layer 5.4
makes over a number field, the discriminant being `1`. It is strictly weaker than the sup-norm form
above, since by Layer 5.1's `Rat.gcd_mul_mulHeight_intCast` the height of an integer tuple is its
sup norm divided by its content, and the basis produced is not primitive in general. -/
theorem exists_linearIndependent_mulVec_eq_zero_prod_mulHeight_le (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) :
    ∃ x : Fin (Fintype.card ι - m) → (ι → ℤ), LinearIndependent ℤ x ∧ (∀ l, A *ᵥ x l = 0) ∧
      (∏ l, Height.mulHeight (((↑) : ℤ → ℚ) ∘ x l)) ≤
        Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ) := by
  obtain ⟨x, hxind, hxA, hxprod⟩ := exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le A hA
  refine ⟨x, hxind, hxA, le_trans (Finset.prod_le_prod₀ (fun l _ ↦ ?_) fun l _ ↦ ?_) hxprod⟩
  · exact (Height.mulHeight_pos _).le
  · have hne : Nonempty ι := Fintype.card_pos_iff.1 (by have := l.isLt; omega)
    exact Rat.mulHeight_intCast_le (hxind.ne_zero l)

/-- **Bombieri–Vaaler's Theorem 1** (Bombieri–Vaaler 1983, Theorem 1; Aliev–Henk §6, Theorem 6.2).
For an `M × N` integer matrix with linearly independent rows and `M < N` there is a nonzero
integral solution of `A x = 0` with sup norm at most `(D⁻¹ √(det (A Aᵀ)))^{1/(N - M)}`.

Unlike the bound of Layer 5.1 this one is invariant under `A ↦ U A` for `U ∈ GL_M(ℤ)`, by
`Int.Matrix.sqrt_det_div_minorGcd_unit_mul`. -/
theorem exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow (A : _root_.Matrix (Fin m) ι ℤ)
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hmn : m < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ((⨆ i, |x i| : ℤ) : ℝ) ≤
        (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ)) ^
          (((Fintype.card ι : ℝ) - m)⁻¹) := by
  have hk0 : Fintype.card ι - m ≠ 0 := by omega
  have hkr : ((Fintype.card ι : ℝ) - m) = ((Fintype.card ι - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmn.le]
  have hD1 : (1 : ℝ) ≤ ((minorGcd A : ℤ) : ℝ) := by exact_mod_cast one_le_minorGcd hA
  have hCpos : 0 < Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ) := by
    refine div_pos (Real.sqrt_pos.2 ?_) (by linarith)
    exact_mod_cast det_pos hA
  obtain ⟨x, hxind, hxA, hxprod⟩ := exists_linearIndependent_mulVec_eq_zero_prod_iSup_abs_le A hA
  have hsnn : ∀ l, 0 ≤ ((⨆ i, |x l i| : ℤ) : ℝ) := by
    intro l
    have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ |x l i|)
    rw [← hi₀]
    exact_mod_cast abs_nonneg (x l i₀)
  have hne : Nonempty (Fin (Fintype.card ι - m)) :=
    Fin.pos_iff_nonempty.1 (Nat.pos_of_ne_zero hk0)
  obtain ⟨l₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (Fintype.card ι - m)))
    (fun l ↦ ((⨆ i, |x l i| : ℤ) : ℝ)) ⟨Classical.arbitrary _, mem_univ _⟩
  have hpow : ((⨆ i, |x l₀ i| : ℤ) : ℝ) ^ (Fintype.card ι - m)
      ≤ Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / ((minorGcd A : ℤ) : ℝ) := by
    calc ((⨆ i, |x l₀ i| : ℤ) : ℝ) ^ (Fintype.card ι - m)
        = ∏ _l : Fin (Fintype.card ι - m), ((⨆ i, |x l₀ i| : ℤ) : ℝ) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ l, ((⨆ i, |x l i| : ℤ) : ℝ) :=
          Finset.prod_le_prod₀ (fun l _ ↦ hsnn l₀) fun l _ ↦ hmin l (mem_univ l)
      _ ≤ _ := hxprod
  refine ⟨x l₀, hxind.ne_zero l₀, hxA l₀, ?_⟩
  rw [hkr]
  refine (pow_le_pow_iff_left₀ (hsnn l₀) (Real.rpow_nonneg hCpos.le _) hk0).1 ?_
  rw [Real.rpow_inv_natCast_pow hCpos.le hk0]
  exact hpow

end Int.Matrix
