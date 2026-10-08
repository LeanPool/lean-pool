/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.AdaptedCell
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# High-contrast homogenization: Entry.Geometry.QuadraticForm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quadratic forms and the Euclidean operator norm

The matrix analysis behind `e.rounded.grid.bounds` is
carried out entirely with quadratic forms `v ⬝ᵥ (M *ᵥ v)` and squared Euclidean norms
`vecNormSq`.  This file provides:

* the symmetric-form identities and the Cauchy–Schwarz inequality for a positive semidefinite
  form, `(x ⬝ᵥ M y)² ≤ (x ⬝ᵥ M x)(y ⬝ᵥ M y)`;
* the bridge between Mathlib's L2 operator norm `‖M‖` (the print's `|M|`) and the vector
  form `|M v|² ≤ ‖M‖² |v|²`, in both directions;
* two consequences for a symmetric positive semidefinite `M`: a bound `⟨v, M v⟩ ≤ K |v|²` on
  the form upgrades to `|M v| ≤ K |v|`, and `c |v|² ≤ ⟨v, M v⟩` upgrades to `c |v| ≤ |M v|`.

The print's `|·|` on matrices is the Euclidean operator norm; Mathlib's scoped instance
`Matrix.Norms.L2Operator` is exactly that norm, and every use of it below goes through the
single inequality `Matrix.l2_opNorm_mulVec`.
-/

namespace HCPolySupport.HighContrast.Geometry

open Matrix
open scoped Matrix.Norms.L2Operator

variable {d : ℕ}

/-! ## Symmetric forms -/

theorem vecNormSq_eq_dotProduct (v : Vec d) : vecNormSq v = v ⬝ᵥ v := rfl

theorem transpose_eq_of_isHermitian {M : Mat d} (hM : Matrix.IsHermitian M) : Mᵀ = M := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact hM.eq

theorem dotProduct_mulVec_nonneg_of_posSemidef {M : Mat d} (hM : Matrix.PosSemidef M) (x : Vec d) :
    0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  have h := hM.dotProduct_mulVec_nonneg x
  rwa [star_trivial] at h

/-- The form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {M : Mat d} (hM : Mᵀ = M) (x y : Vec d) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

/-- For symmetric `M`, `|M v|² = ⟨v, M² v⟩`. -/
theorem vecNormSq_mulVec_eq {M : Mat d} (hM : Mᵀ = M) (v : Vec d) :
    vecNormSq (M *ᵥ v) = v ⬝ᵥ ((M * M) *ᵥ v) := by
  rw [vecNormSq_eq_dotProduct, ← mulVec_mulVec]
  exact (dotProduct_mulVec_comm hM v _).symm

/-- Cauchy–Schwarz for a positive semidefinite form. -/
theorem sq_dotProduct_mulVec_le {M : Mat d} (hM : Mᵀ = M)
    (hpos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (M *ᵥ x)) (x y : Vec d) :
    (x ⬝ᵥ (M *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (M *ᵥ x)) * (y ⬝ᵥ (M *ᵥ y)) := by
  set a := x ⬝ᵥ (M *ᵥ x) with ha
  set b := x ⬝ᵥ (M *ᵥ y) with hb
  set c := y ⬝ᵥ (M *ᵥ y) with hc
  have key : ∀ t : ℝ, 0 ≤ c * (t * t) + (2 * b) * t + a := by
    intro t
    have h := hpos (x + t • y)
    have hexp : (x + t • y) ⬝ᵥ (M *ᵥ (x + t • y)) = c * (t * t) + (2 * b) * t + a := by
      rw [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, dotProduct_add,
        dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_mulVec_comm hM y x]
      simp only [smul_eq_mul, ha, hb, hc]
      ring
    rw [hexp] at h
    exact h
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith only [hd]

/-! ## The operator norm bridge -/

theorem norm_toLp_sq (v : Vec d) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ^ 2 = vecNormSq v := by
  rw [EuclideanSpace.norm_sq_eq, vecNormSq_eq_sum_sq]
  simp [Real.norm_eq_abs, sq_abs]

/-- `|M v|² ≤ ‖M‖² |v|²` for the Euclidean operator norm. -/
theorem vecNormSq_mulVec_le_opNorm (M : Mat d) (v : Vec d) :
    vecNormSq (M *ᵥ v) ≤ ‖M‖ ^ 2 * vecNormSq v := by
  have h := M.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have h1 : ‖(EuclideanSpace.equiv (Fin d) ℝ).symm
      (M *ᵥ (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)))‖ ^ 2 = vecNormSq (M *ᵥ v) :=
    norm_toLp_sq (M *ᵥ v)
  have h2 := norm_toLp_sq v
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [h1, mul_pow, h2] at this
  exact this

/-- The converse: a uniform bound `|M v|² ≤ K² |v|²` bounds the operator norm. -/
theorem opNorm_le_of_vecNormSq_mulVec_le {M : Mat d} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Vec d, vecNormSq (M *ᵥ v) ≤ K ^ 2 * vecNormSq v) : ‖M‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  have hx := h (WithLp.ofLp x)
  rw [← norm_toLp_sq, ← norm_toLp_sq] at hx
  have h2 : ‖(WithLp.toLp 2 (M *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ (Fin d))‖ ^ 2
      ≤ (K * ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ (Fin d))‖) ^ 2 := by
    rw [mul_pow]
    exact hx
  have h3 := (abs_le_of_sq_le_sq' h2 (by positivity)).2
  simpa using! h3

/-! ## Form bounds from vector bounds and back -/

/-- A vector bound `|M v| ≤ K |v|` bounds the form: `|⟨v, M v⟩| ≤ K |v|²`. -/
theorem abs_dotProduct_mulVec_le_of_vecNormSq_le {M : Mat d} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Vec d, vecNormSq (M *ᵥ v) ≤ K ^ 2 * vecNormSq v) (v : Vec d) :
    |v ⬝ᵥ (M *ᵥ v)| ≤ K * vecNormSq v := by
  have h1 := sq_vecDot_le_vecNormSq_mul_vecNormSq v (M *ᵥ v)
  have h2 := h v
  have hv := vecNormSq_nonneg v
  have h3 : (v ⬝ᵥ (M *ᵥ v)) ^ 2 ≤ (K * vecNormSq v) ^ 2 := by
    calc (v ⬝ᵥ (M *ᵥ v)) ^ 2 ≤ vecNormSq v * vecNormSq (M *ᵥ v) := h1
      _ ≤ vecNormSq v * (K ^ 2 * vecNormSq v) := by gcongr
      _ = (K * vecNormSq v) ^ 2 := by ring
  exact abs_le_of_sq_le_sq h3 (by positivity)

/-- `⟨v, M v⟩ ≤ ‖M‖ |v|²`. -/
theorem dotProduct_mulVec_le_opNorm (M : Mat d) (v : Vec d) :
    v ⬝ᵥ (M *ᵥ v) ≤ ‖M‖ * vecNormSq v :=
  (le_abs_self _).trans
    (abs_dotProduct_mulVec_le_of_vecNormSq_le (norm_nonneg M)
      (vecNormSq_mulVec_le_opNorm M) v)

/-- For a symmetric matrix `R` with `R * R = P`: `⟨u, R u⟩ ≤ √‖P‖ |u|²`. -/
theorem dotProduct_mulVec_le_sqrt_opNorm_sq {R P : Mat d} (hR : Rᵀ = R) (hRP : R * R = P)
    (u : Vec d) : u ⬝ᵥ (R *ᵥ u) ≤ Real.sqrt ‖P‖ * vecNormSq u := by
  have h1 := sq_vecDot_le_vecNormSq_mul_vecNormSq u (R *ᵥ u)
  have h2 : vecNormSq (R *ᵥ u) ≤ ‖P‖ * vecNormSq u := by
    rw [vecNormSq_mulVec_eq hR, hRP]
    exact dotProduct_mulVec_le_opNorm P u
  have hu := vecNormSq_nonneg u
  have hP : Real.sqrt ‖P‖ ^ 2 = ‖P‖ := Real.sq_sqrt (norm_nonneg P)
  have h3 : (u ⬝ᵥ (R *ᵥ u)) ^ 2 ≤ (Real.sqrt ‖P‖ * vecNormSq u) ^ 2 := by
    calc (u ⬝ᵥ (R *ᵥ u)) ^ 2 ≤ vecNormSq u * vecNormSq (R *ᵥ u) := h1
      _ ≤ vecNormSq u * (‖P‖ * vecNormSq u) := by gcongr
      _ = (Real.sqrt ‖P‖ * vecNormSq u) ^ 2 := by rw [mul_pow, hP]; ring
  exact (abs_le_of_sq_le_sq' h3 (by positivity)).2

/-- For a symmetric positive semidefinite `M`, a bound `⟨x, M x⟩ ≤ K |x|²` on the form gives
the vector bound `|M v|² ≤ K² |v|²`. -/
theorem vecNormSq_mulVec_le_of_dotProduct_le {M : Mat d} (hM : Mᵀ = M)
    (hpos : ∀ x : Vec d, 0 ≤ x ⬝ᵥ (M *ᵥ x)) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x : Vec d, x ⬝ᵥ (M *ᵥ x) ≤ K * vecNormSq x) (v : Vec d) :
    vecNormSq (M *ᵥ v) ≤ K ^ 2 * vecNormSq v := by
  have hcs := sq_dotProduct_mulVec_le hM hpos v (M *ᵥ v)
  have heq : v ⬝ᵥ (M *ᵥ (M *ᵥ v)) = vecNormSq (M *ᵥ v) := by
    rw [vecNormSq_mulVec_eq hM, mulVec_mulVec]
  rw [heq] at hcs
  have h1 := h v
  have h2 := h (M *ᵥ v)
  have hv := vecNormSq_nonneg v
  have hMv := vecNormSq_nonneg (M *ᵥ v)
  have h3 : vecNormSq (M *ᵥ v) * vecNormSq (M *ᵥ v)
      ≤ (K ^ 2 * vecNormSq v) * vecNormSq (M *ᵥ v) := by
    calc vecNormSq (M *ᵥ v) * vecNormSq (M *ᵥ v) = vecNormSq (M *ᵥ v) ^ 2 := by ring
      _ ≤ (v ⬝ᵥ (M *ᵥ v)) * ((M *ᵥ v) ⬝ᵥ (M *ᵥ (M *ᵥ v))) := hcs
      _ ≤ (K * vecNormSq v) * (K * vecNormSq (M *ᵥ v)) :=
          mul_le_mul h1 h2 (hpos _) (by positivity)
      _ = (K ^ 2 * vecNormSq v) * vecNormSq (M *ᵥ v) := by ring
  rcases eq_or_lt_of_le hMv with h0 | h0
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right h3 h0

/-- A lower bound `c |x|² ≤ ⟨x, M x⟩` on the form gives `c² |v|² ≤ |M v|²`. -/
theorem vecNormSq_le_vecNormSq_mulVec_of_le_dotProduct {M : Mat d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Vec d, c * vecNormSq x ≤ x ⬝ᵥ (M *ᵥ x)) (v : Vec d) :
    c ^ 2 * vecNormSq v ≤ vecNormSq (M *ᵥ v) := by
  have h1 := sq_vecDot_le_vecNormSq_mul_vecNormSq v (M *ᵥ v)
  have h2 := h v
  have hv := vecNormSq_nonneg v
  have h3 : (c * vecNormSq v) ^ 2 ≤ vecNormSq v * vecNormSq (M *ᵥ v) :=
    (pow_le_pow_left₀ (by positivity) h2 2).trans h1
  rcases eq_or_lt_of_le hv with h0 | h0
  · rw [← h0, mul_zero]
    exact vecNormSq_nonneg _
  · have h4 : (c ^ 2 * vecNormSq v) * vecNormSq v ≤ vecNormSq (M *ᵥ v) * vecNormSq v := by
      have e : (c * vecNormSq v) ^ 2 = (c ^ 2 * vecNormSq v) * vecNormSq v := by ring
      linarith only [h3, e, mul_comm (vecNormSq v) (vecNormSq (M *ᵥ v))]
    exact le_of_mul_le_mul_right h4 h0

end HCPolySupport.HighContrast.Geometry
