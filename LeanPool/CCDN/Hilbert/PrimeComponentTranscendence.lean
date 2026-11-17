/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IdealZeroLocus
public import LeanPool.CCDN.ForMathlib.KrullHeight
public import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.Hilbert.FilteredHilbertLinearity
import Mathlib.FieldTheory.Minpoly.Basic

/-! A point on a prime component forces a transcendental coordinate and
 positive eventual Hilbert slope in codimension two. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Evaluate the first `n` coordinates, leaving all later coordinates free. -/
def partialCoordinateEval {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  eval₂Hom C (fun j => if j.val < n then C (c j) else X j)

/-- `partialCoordinateEval c n` fixes constants. -/
@[simp] lemma partialCoordinateEval_C {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) (a : K) :
    partialCoordinateEval c n (C a) = C a := by simp [partialCoordinateEval]

/-- `partialCoordinateEval c n` replaces `X j` by `c j` for `j < n` and fixes the other variables.
-/
@[simp] lemma partialCoordinateEval_X {K : Type*} [CommRing K] (c : Fin 3 → K) (n : ℕ) (j : Fin 3) :
    partialCoordinateEval c n (X j) = if j.val < n then C (c j) else X j := by
  simp [partialCoordinateEval]

private lemma partialCoordinateEval_comp {K : Type*} [CommRing K] (c : Fin 3 → K)
    {m n : ℕ} (hmn : m ≤ n) :
    (partialCoordinateEval c n).comp (partialCoordinateEval c m) = partialCoordinateEval c n := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro j
    by_cases hj : j.val < m
    · have hn : j.val < n := lt_of_lt_of_le hj hmn
      simp [hj, hn]
    · simp [hj]

private lemma partialCoordinateEval_ker_lt {K : Type*} [Field K] (c : Fin 3 → K)
    {n : ℕ} (hn : n < 3) :
    RingHom.ker (partialCoordinateEval c n) < RingHom.ker (partialCoordinateEval c (n + 1)) := by
  have hle : RingHom.ker (partialCoordinateEval c n) ≤
      RingHom.ker (partialCoordinateEval c (n + 1)) := by
    intro f hf
    change partialCoordinateEval c n f = 0 at hf
    have hcomp := congrArg (fun φ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K => φ f)
      (partialCoordinateEval_comp c (show n ≤ n + 1 by omega))
    change partialCoordinateEval c (n + 1) (partialCoordinateEval c n f) = _ at hcomp
    rw [hf, map_zero] at hcomp
    exact hcomp.symm
  apply lt_of_le_of_ne hle
  intro heq
  let j : Fin 3 := ⟨n, hn⟩
  have hmem : X j - C (c j) ∈ RingHom.ker (partialCoordinateEval c (n + 1)) := by
    simp [RingHom.mem_ker, j]
  rw [← heq] at hmem
  have hzero : (X j - C (c j) : MvPolynomial (Fin 3) K) = 0 := by
    simpa [RingHom.mem_ker, j] using hmem
  have hc := congrArg (fun p : MvPolynomial (Fin 3) K => p.coeff (Finsupp.single j 1)) hzero
  have hsingle : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h
    have := DFunLike.congr_fun h j
    simp at this
  simp [hsingle] at hc

/-- Fixing all three coordinates gives a prime ideal of height at least three. -/
private lemma three_le_height_coordinate_kernel {K : Type*} [Field K] (c : Fin 3 → K) :
    3 ≤ (RingHom.ker (partialCoordinateEval c 3)).height := by
  let inst (n : ℕ) : (RingHom.ker (partialCoordinateEval c n)).IsPrime := RingHom.ker_isPrime _
  have h0 := Ideal.height_add_one_le_of_lt_of_isPrime
    (partialCoordinateEval_ker_lt c (n := 0) (by omega))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
    (partialCoordinateEval_ker_lt c (n := 1) (by omega))
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
    (partialCoordinateEval_ker_lt c (n := 2) (by omega))
  have h01 : (1 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval c 1)).height := by
    calc
      1 = (0 : ℕ∞) + 1 := by norm_num
      _ ≤ (RingHom.ker (partialCoordinateEval c 0)).height + 1 := by gcongr; exact bot_le
      _ ≤ _ := h0
  have h12 : (2 : ℕ∞) ≤ (RingHom.ker (partialCoordinateEval c 2)).height := by
    calc
      2 = (1 : ℕ∞) + 1 := by norm_num
      _ ≤ (RingHom.ker (partialCoordinateEval c 1)).height + 1 := by gcongr
      _ ≤ _ := h1
  calc
    3 = (2 : ℕ∞) + 1 := by norm_num
    _ ≤ (RingHom.ker (partialCoordinateEval c 2)).height + 1 := by gcongr
    _ ≤ _ := h2

/-- An algebraic element detected by a base-field-valued point is scalar. -/
lemma algebraic_eq_scalar_of_point {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (φ : A →ₐ[K] K) {y : A} (hy : IsAlgebraic K y) :
    algebraMap K A (φ y) = y := by
  have hi := hy.isIntegral
  have hroot : (minpoly K y).IsRoot (φ y) := by
    have he := Polynomial.aeval_algHom_apply φ y (minpoly K y)
    rw [minpoly.aeval, map_zero] at he
    simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using he
  have hassoc := (Polynomial.irreducible_X_sub_C (φ y)).associated_of_dvd
    (minpoly.irreducible hi) (Polynomial.dvd_iff_isRoot.mpr hroot)
  have he : Polynomial.aeval y (Polynomial.X - Polynomial.C (φ y)) = 0 := by
    obtain ⟨r, hr⟩ := hassoc.symm.dvd
    rw [hr, map_mul, minpoly.aeval, zero_mul]
  simpa using (sub_eq_zero.mp (by simpa using he)).symm

/-- Evaluation at a rational point descends to its prime coordinate ring. -/
def coordinatePoint {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p) :
    (MvPolynomial σ K ⧸ p) →ₐ[K] K :=
  Ideal.Quotient.liftₐ p (MvPolynomial.aeval z) (by
    intro f hf
    simpa only [MvPolynomial.aeval_eq_eval] using hz f hf)

/-- Evaluation at the point `z` sends the class of `f` to `f(z)`. -/
@[simp] lemma coordinatePoint_mk {K σ : Type*} [Field K]
    (p : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∈ idealZeroLocus p)
    (f : MvPolynomial σ K) :
    coordinatePoint p z hz ((Ideal.Quotient.mk p) f) = MvPolynomial.eval z f := by
  simp [coordinatePoint, Ideal.Quotient.liftₐ_apply]

/-- A height-two prime in three variables containing a rational point retains a
transcendental coordinate over its base field. -/
theorem height_two_transcendental_coordinate_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) :
    ∃ j : Fin 3, Transcendental K ((Ideal.Quotient.mk p) (X j)) := by
  classical
  by_contra h
  push Not at h
  have ha (j : Fin 3) : IsAlgebraic K ((Ideal.Quotient.mk p) (X j)) := by
    simpa only [Transcendental, not_not] using h j
  have hc (j : Fin 3) : algebraMap K (MvPolynomial (Fin 3) K ⧸ p) (z j) =
      (Ideal.Quotient.mk p) (X j) := by
    simpa using algebraic_eq_scalar_of_point (coordinatePoint p z hz) (ha j)
  have hcomp : (Ideal.Quotient.mk p).comp (partialCoordinateEval z 3) = Ideal.Quotient.mk p := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [RingHom.comp_apply, partialCoordinateEval_X, ite_eq_left j.isLt]
      exact hc j
  have hle : RingHom.ker (partialCoordinateEval z 3) ≤ p := by
    intro f hf
    change partialCoordinateEval z 3 f = 0 at hf
    have he := congrArg (fun φ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K ⧸ p => φ f) hcomp
    change (Ideal.Quotient.mk p) (partialCoordinateEval z 3 f) = _ at he
    rw [hf, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm
  have hd := (three_le_height_coordinate_kernel z).trans (Ideal.height_mono hle)
  rw [hp] at hd
  norm_num at hd

/-- A height-two component with a base-field point has positive slope in
 any eventual linear Hilbert formula, independently of its cutoff. -/
theorem height_two_eventual_slope_pos_of_point {K : Type*} [Field K]
    (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime] (hp : p.height = 2)
    (z : Fin 3 → K) (hz : z ∈ idealZeroLocus p) {d : ℕ}
    (hlinear : HasFilteredCurveDegree p d) :
    0 < d := by
  obtain ⟨N, c, hlinear⟩ := hlinear
  obtain ⟨j, hj⟩ := height_two_transcendental_coordinate_of_point p hp z hz
  by_contra h
  have hd0 : d = 0 := by omega
  have hlo := transcendental_coordinate_filtered_lower p hj (N + c.natAbs)
  have hhi := hlinear (N + c.natAbs) (by omega)
  rw [hd0] at hhi
  simp only [Nat.cast_zero, zero_mul, zero_add] at hhi
  have habs : c ≤ (c.natAbs : ℤ) := Int.le_natAbs
  have hlo' : ((N + c.natAbs + 1 : ℕ) : ℤ) ≤
      (Module.finrank K (filteredCoordinateSpace p (N + c.natAbs)) : ℤ) := by exact_mod_cast hlo
  push_cast at hlo'
  omega

end
end CCDN
