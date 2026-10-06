/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains

/-!
# High-contrast homogenization: Analytic.EllipsoidGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Non-degeneracy of the ellipsoids `E_r`

The ellipsoids
`E_r = {x : x · s_bar⁻¹ x ≤ λ_bar⁻¹ r²}`
of `e.homogenized.ellipsoids` are the domains on
which the corrector estimate
`e.random.corrector`, the Lipschitz
estimate `e.random.energy` and the
`C^{1,ϑ}` estimate `e.random.regularity` are read.
Each of those is written through a volume-normalized average over `E_r`, and
such an average carries the intended meaning only when `E_r` is a measurable set
of positive finite volume.  This module proves exactly that, together with the
Loewner and positive-definiteness facts that the proof consumes.

The two halves are separately elementary.

* Positive volume is unconditional.  The scalar Loewner bound
  `x · M x ≤ |M| ‖x‖²` holds for every matrix, so `E_r` contains the concentric
  Euclidean ball of radius `r`, which is open and nonempty for `r > 0`.  No
  positivity, symmetry or invertibility hypothesis on `ā` is used.
* Finite volume needs the positive definiteness of the symmetric part `s_bar`, and
  follows from the reverse bound `‖x‖² ≤ (x · s_bar⁻¹ x) |s_bar|`.  That bound is
  Cauchy–Schwarz for the positive semidefinite form of `s_bar⁻¹` applied to the
  pair `(x, s_bar x)`; no eigenvalue theory enters.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-! ## The scalar Loewner bound in quadratic-form shape

`matLoewnerLE_specBound_smul_one` is unconditional: every matrix satisfies
`M ≤ |M| · I` in the Loewner order.  Written on the quadratic form this is the
pointwise bound `x · M x ≤ |M| ‖x‖²`, which is the only ingredient the ellipsoid
inclusion needs. -/

/-- Multiplication by a scalar multiple of the identity. -/
theorem matVecMul_smul_one' (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

/-- **The unconditional scalar Loewner bound**, on the quadratic form.  No
hypothesis on `M` whatsoever. -/
theorem vecDot_matVecMul_le_specBound_mul_vecNormSq (M : Mat d) (x : Vec d) :
    vecDot x (matVecMul M x) ≤ specBound M * vecNormSq x := by
  have h := matLoewnerLE_specBound_smul_one M x
  rw [matVecMul_smul_one', vecDot_smul_right] at h
  have hnorm : vecDot x x = vecNormSq x := rfl
  rw [hnorm] at h
  linarith only [h]

/-! ## The Euclidean ball sits inside the ellipsoid

This holds for **every** `abar`, with no positivity, symmetry or invertibility
hypothesis: on `euclideanBallAt 0 r` one has `‖x‖² < r²`, the Loewner bound gives
`x · s_bar⁻¹ x ≤ |s_bar⁻¹| ‖x‖²`, and `|s_bar⁻¹| ≥ 0` (`specBound_nonneg`, also
unconditional) lets the two be multiplied. -/

/-- **The ellipsoid contains the concentric Euclidean ball of the same radius**,
unconditionally. -/
theorem euclideanBallAt_zero_subset_ellipsoid (abar : Mat d) (r : ℝ) :
    euclideanBallAt (0 : Vec d) r ⊆ ellipsoid abar r := by
  intro x hx
  have hx' : vecNormSq x < r ^ 2 := by
    have : vecNormSq (x - 0) < r ^ 2 := hx
    rwa [sub_zero] at this
  have hb := vecDot_matVecMul_le_specBound_mul_vecNormSq ((symmPart abar)⁻¹) x
  have hc : (0 : ℝ) ≤ specBound ((symmPart abar)⁻¹) := specBound_nonneg _
  have hmul : specBound ((symmPart abar)⁻¹) * vecNormSq x ≤
      specBound ((symmPart abar)⁻¹) * r ^ 2 :=
    mul_le_mul_of_nonneg_left hx'.le hc
  show vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤ specBound ((symmPart abar)⁻¹) * r ^ 2
  linarith only [hb, hmul]

/-! ## The bridge to `Matrix.PosDef` -/

/-- `symmPart` is Hermitian by construction. -/
theorem isHermitian_symmPart (A : Mat d) : (symmPart A).IsHermitian := by
  show (symmPart A)ᴴ = symmPart A
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, symmPart]
  ring

/-- **The bridge.**  The elementwise positivity statement of the Dirichlet
clause is Mathlib's `Matrix.PosDef` for the symmetric part.  `star x ⬝ᵥ M *ᵥ x`
and `vecDot x (matVecMul M x)` are definitionally equal on `Vec d`. -/
theorem posDef_symmPart_of_vecDot_pos {abar : Mat d}
    (hpd : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) :
    (symmPart abar).PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_symmPart abar) fun _ hx => hpd _ hx

/-- The converse reading of `Matrix.PosDef` on `Vec d`. -/
theorem vecDot_matVecMul_pos_of_posDef {M : Mat d} (hM : M.PosDef) {x : Vec d}
    (hx : x ≠ 0) : 0 < vecDot x (matVecMul M x) :=
  hM.dotProduct_mulVec_pos hx

/-! ## Measurability, the centre, and positive volume -/

/-- The ellipsoid quadratic form is continuous. -/
theorem continuous_vecDot_matVecMul (M : Mat d) :
    Continuous fun x : Vec d => vecDot x (matVecMul M x) := by
  simp only [vecDot, matVecMul]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul
      (continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j))

/-- The ellipsoid is closed. -/
theorem isClosed_ellipsoid (abar : Mat d) (r : ℝ) : IsClosed (ellipsoid abar r) :=
  isClosed_le (continuous_vecDot_matVecMul _) continuous_const

/-- The ellipsoid is measurable. -/
theorem measurableSet_ellipsoid (abar : Mat d) (r : ℝ) :
    MeasurableSet (ellipsoid abar r) :=
  (isClosed_ellipsoid abar r).measurableSet

/-- The centre lies in every ellipsoid; no sign condition on `r` and no
hypothesis on `abar` is needed. -/
theorem zero_mem_ellipsoid (abar : Mat d) (r : ℝ) :
    (0 : Vec d) ∈ ellipsoid abar r := by
  show vecDot (0 : Vec d) (matVecMul (symmPart abar)⁻¹ 0) ≤
    specBound ((symmPart abar)⁻¹) * r ^ 2
  have hzero : vecDot (0 : Vec d) (matVecMul (symmPart abar)⁻¹ 0) = 0 := by
    simp [vecDot]
  rw [hzero]
  exact mul_nonneg (specBound_nonneg _) (sq_nonneg r)

/-- The ellipsoid has positive volume for positive radius; no hypothesis on
`abar` is needed, because the ellipsoid contains the concentric Euclidean ball
of the same radius. -/
theorem volume_ellipsoid_pos (abar : Mat d) {r : ℝ} (hr : 0 < r) :
    0 < volume (ellipsoid abar r) :=
  lt_of_lt_of_le
    (IsOpen.measure_pos volume (isOpen_euclideanBallAt (0 : Vec d) r)
      ⟨(0 : Vec d), center_mem_euclideanBallAt (0 : Vec d) hr⟩)
    (measure_mono (euclideanBallAt_zero_subset_ellipsoid abar r))

/-! ## The reverse Loewner bound, and finite volume -/

/-- The inverse quadratic form of a positive definite matrix is nonnegative. -/
theorem vecDot_matVecMul_inv_nonneg {S : Mat d} (hS : S.PosDef) (x : Vec d) :
    0 ≤ vecDot x (matVecMul S⁻¹ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [vecDot]
  · exact (vecDot_matVecMul_pos_of_posDef hS.inv hx).le

/-- **The reverse Loewner bound of a positive definite matrix**, obtained from
Cauchy–Schwarz for the positive semidefinite form of `S⁻¹` — no eigenvalue
theory is used:
`‖x‖⁴ = (x · S⁻¹ (S x))² ≤ (x · S⁻¹ x)(S x · S⁻¹ S x) = (x · S⁻¹ x)(x · S x)`. -/
theorem vecNormSq_le_vecDot_matVecMul_inv_mul_specBound {S : Mat d} (hS : S.PosDef)
    (x : Vec d) :
    vecNormSq x ≤ vecDot x (matVecMul S⁻¹ x) * specBound S := by
  have hu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit
  have hsymm : (S⁻¹).IsSymm := isSymm_nonsingInv (isSymm_of_isHermitian hS.1)
  have hid : matVecMul S⁻¹ (matVecMul S x) = x := by
    rw [matVecMul_mul, Matrix.nonsing_inv_mul _ hu, matVecMul_one]
  have hcs := sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hsymm
    (vecDot_matVecMul_inv_nonneg hS) x (matVecMul S x)
  rw [hid] at hcs
  have hleft : vecDot x x = vecNormSq x := rfl
  rw [hleft] at hcs
  have hright : vecDot (matVecMul S x) x = vecDot x (matVecMul S x) :=
    vecDot_comm _ _
  rw [hright] at hcs
  have ha : 0 ≤ vecDot x (matVecMul S⁻¹ x) := vecDot_matVecMul_inv_nonneg hS x
  have hq : vecDot x (matVecMul S x) ≤ specBound S * vecNormSq x :=
    vecDot_matVecMul_le_specBound_mul_vecNormSq S x
  have hstep : vecNormSq x ^ 2 ≤
      vecDot x (matVecMul S⁻¹ x) * (specBound S * vecNormSq x) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hq ha)
  rcases eq_or_lt_of_le (vecNormSq_nonneg x) with hN | hN
  · rw [← hN]
    exact mul_nonneg ha (specBound_nonneg S)
  · refine le_of_mul_le_mul_right ?_ hN
    calc vecNormSq x * vecNormSq x = vecNormSq x ^ 2 := (pow_two _).symm
      _ ≤ vecDot x (matVecMul S⁻¹ x) * (specBound S * vecNormSq x) := hstep
      _ = vecDot x (matVecMul S⁻¹ x) * specBound S * vecNormSq x := by ring

/-- Every point of the ellipsoid obeys an explicit Euclidean bound. -/
theorem vecNormSq_le_of_mem_ellipsoid {abar : Mat d} (hS : (symmPart abar).PosDef)
    {r : ℝ} {x : Vec d} (hx : x ∈ ellipsoid abar r) :
    vecNormSq x ≤
      specBound ((symmPart abar)⁻¹) * r ^ 2 * specBound (symmPart abar) := by
  have hx' : vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤
      specBound ((symmPart abar)⁻¹) * r ^ 2 := hx
  calc vecNormSq x
      ≤ vecDot x (matVecMul (symmPart abar)⁻¹ x) * specBound (symmPart abar) :=
        vecNormSq_le_vecDot_matVecMul_inv_mul_specBound hS x
    _ ≤ specBound ((symmPart abar)⁻¹) * r ^ 2 * specBound (symmPart abar) :=
        mul_le_mul_of_nonneg_right hx' (specBound_nonneg _)

/-- The ellipsoid is a bounded domain. -/
theorem isBoundedDomain_ellipsoid {abar : Mat d} (hS : (symmPart abar).PosDef)
    (r : ℝ) : IsBoundedDomain (ellipsoid abar r) := by
  refine ⟨Real.sqrt
    (specBound ((symmPart abar)⁻¹) * r ^ 2 * specBound (symmPart abar)) + 1,
    by positivity, fun x hx i => ?_⟩
  have hN := vecNormSq_le_of_mem_ellipsoid hS hx
  have h1 : x i ^ 2 ≤ vecNormSq x := sq_apply_le_vecNormSq x i
  have h2 : x i ^ 2 ≤
      specBound ((symmPart abar)⁻¹) * r ^ 2 * specBound (symmPart abar) :=
    le_trans h1 hN
  have h3 : |x i| ≤ Real.sqrt
      (specBound ((symmPart abar)⁻¹) * r ^ 2 * specBound (symmPart abar)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h2
  have h4 : (0 : ℝ) ≤ Real.sqrt
      (specBound ((symmPart abar)⁻¹) * r ^ 2 * specBound (symmPart abar)) :=
    Real.sqrt_nonneg _
  linarith only [h3, h4]

/-- The ellipsoid is bornologically bounded. -/
theorem isBounded_ellipsoid {abar : Mat d} (hS : (symmPart abar).PosDef) (r : ℝ) :
    Bornology.IsBounded (ellipsoid abar r) := by
  obtain ⟨R, hR0, hR⟩ := isBoundedDomain_ellipsoid hS r
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R, fun x hx => ?_⟩
  refine Metric.mem_closedBall.2 ?_
  rw [dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg hR0.le).2 fun i => ?_
  simpa only [Real.norm_eq_abs] using hR x hx i

/-- The ellipsoid has finite volume. -/
theorem volume_ellipsoid_lt_top {abar : Mat d} (hS : (symmPart abar).PosDef)
    (r : ℝ) : volume (ellipsoid abar r) < ⊤ :=
  (isBounded_ellipsoid hS r).measure_lt_top

/-- **The non-degeneracy statement.**  Under the positivity of the symmetric
part of `ā`, every ellipsoid of positive radius is a measurable set of positive
finite volume containing the origin, so the volume-normalized averages read on
`E_r` are neither `0/0` nor `∞/∞`. -/
theorem ellipsoid_nondegenerate {abar : Mat d}
    (hpd : ∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x))
    {r : ℝ} (hr : 0 < r) :
    (0 : Vec d) ∈ ellipsoid abar r ∧ MeasurableSet (ellipsoid abar r) ∧
      IsBoundedDomain (ellipsoid abar r) ∧
      0 < volume (ellipsoid abar r) ∧ volume (ellipsoid abar r) < ⊤ :=
  ⟨zero_mem_ellipsoid abar r, measurableSet_ellipsoid abar r,
    isBoundedDomain_ellipsoid (posDef_symmPart_of_vecDot_pos hpd) r,
    volume_ellipsoid_pos abar hr,
    volume_ellipsoid_lt_top (posDef_symmPart_of_vecDot_pos hpd) r⟩

end

end HighContrast
end HCPolySupport
