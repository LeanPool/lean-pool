/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

-- Modified for Lean Pool.

module

public import LeanPool.TetrahedronPacking.IntegerCertificate
public import LeanPool.TetrahedronPacking.RecordArithmetic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The published packing in real space

Use the integer scale from `RecordArithmetic` in all three directions. The
adjugate of the period matrix maps the vertices into a coordinate box of
width strictly less than three after division by the determinant. Thus a
common point of two hulls forces all three integer shift coordinates into
[-2, 2]. The integer plane witnesses then separate the interiors in ℝ³.
-/

@[expose] public section

namespace TetrahedronPacking

open Set Matrix
open MeasureTheory

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail

/-- The columns are the three primitive period vectors. -/
def periodMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (recordPeriod j i : ℝ)

/-- The adjugate of the period matrix, with integer entries. -/
def inverseNumerator : Matrix (Fin 3) (Fin 3) ℤ :=
  !![84132, 297648, -164376;
    -200448, 27648, 317952;
    274176, -202752, 59904]

/-- The inverse of the period matrix, used to express vertices in lattice coordinates. -/
noncomputable def inverseMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  (172191744 : ℝ)⁻¹ • Matrix.map inverseNumerator (fun z : ℤ => (z : ℝ))

example : periodMatrix 0 1 = 90 ∧ periodMatrix 0 1 ≠ 576 := by
  norm_num [periodMatrix, recordPeriod]
example : inverseMatrix 0 0 = 84132 / 172191744 ∧ inverseMatrix 0 0 ≠ 0 := by
  norm_num [inverseMatrix, inverseNumerator, div_eq_mul_inv, mul_comm]

theorem period_mul_inverse : periodMatrix * inverseMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      periodMatrix, inverseMatrix, inverseNumerator, recordPeriod]

theorem inverse_mul_period : inverseMatrix * periodMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      periodMatrix, inverseMatrix, inverseNumerator, recordPeriod]

private theorem period_determinant : periodMatrix.det = 172191744 := by
  norm_num [Matrix.det_fin_three, periodMatrix, recordPeriod]

/-- World to lattice coordinates, in the integer-scaled copy of the packing. -/
noncomputable def recordCoordinates : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin'OfInv period_mul_inverse inverse_mul_period

theorem recordCoordinates_symm_apply (x : Fin 3 → ℝ) (r : Fin 3) :
    recordCoordinates.symm x r = ∑ j : Fin 3, (recordPeriod j r : ℝ) * x j := rfl

/-- The real vertices, still in the uniform integer scale. -/
def recordRealVertex (i a : Fin 4) (j : Fin 3) : ℝ :=
  (recordVertex i a j : ℝ)

example : recordCoordinates.symm ![1, 0, 0] 2 = 192 ∧
    recordCoordinates.symm ![1, 0, 0] 2 ≠ 0 := by
  change (periodMatrix *ᵥ ![1, 0, 0]) 2 = 192 ∧ (periodMatrix *ᵥ ![1, 0, 0]) 2 ≠ 0
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, periodMatrix, recordPeriod]

theorem record_period_cell_volume :
    volume.real (ZSpan.fundamentalDomain ((Pi.basisFun ℝ (Fin 3)).map recordCoordinates.symm)) =
      172191744 := by
  rw [ZSpan.volume_real_fundamentalDomain]
  have h : Matrix.of ((Pi.basisFun ℝ (Fin 3)).map recordCoordinates.symm) =
      periodMatrix.transpose := by
    ext i j
    change (recordCoordinates.symm ((Pi.basisFun ℝ (Fin 3)) i)) j = periodMatrix j i
    rw [Pi.basisFun_apply]
    change (periodMatrix *ᵥ Pi.single i (1 : ℝ)) j = periodMatrix j i
    rw [Matrix.mulVec_single_one]
    rfl
  rw [h, Matrix.det_transpose, period_determinant]
  norm_num

example : recordRealVertex 2 0 2 = -343 ∧ recordRealVertex 2 0 2 ≠ 343 := by
  norm_num [recordRealVertex, recordVertex]

theorem record_squared_edge_lengths (i a b : Fin 4) (h : a ≠ b) :
    ∑ j : Fin 3, (recordRealVertex i a j - recordRealVertex i b j) ^ 2 = 460800 := by
  have hz := record_integer_edge_lengths i a b h
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
  simpa [recordRealVertex, integerDot, Fin.sum_univ_three, pow_two] using hr

/-- The determinant of the three edges out of vertex zero has the same
absolute value for all four regular tetrahedra. -/
theorem record_edge_determinant (i : Fin 4) :
    |(Matrix.of (fun r (s : Fin 3) =>
      recordRealVertex i s.succ r - recordRealVertex i 0 r)).det| = 221184000 := by
  fin_cases i <;>
    norm_num [Matrix.det_fin_three, recordRealVertex, recordVertex,
      Fin.succ]

private theorem record_coordinate_numerators (i a : Fin 4) (j : Fin 3) :
    -258287616 ≤ integerDot (inverseNumerator j) (recordVertex i a) ∧
      5 * integerDot (inverseNumerator j) (recordVertex i a) ≤ 1205342208 := by
  revert i a j
  decide

private theorem record_coordinate_bounds (i a : Fin 4) (j : Fin 3) :
    -3 / 2 ≤ recordCoordinates (recordRealVertex i a) j ∧
      recordCoordinates (recordRealVertex i a) j ≤ 7 / 5 := by
  have h := record_coordinate_numerators i a j
  have hlo : (-258287616 : ℝ) ≤ (integerDot (inverseNumerator j) (recordVertex i a) : ℝ) := by
    exact_mod_cast h.1
  have hhi : (5 : ℝ) * (integerDot (inverseNumerator j) (recordVertex i a) : ℝ) ≤
      1205342208 := by exact_mod_cast h.2
  have hcoord : recordCoordinates (recordRealVertex i a) j =
      (172191744 : ℝ)⁻¹ * (integerDot (inverseNumerator j) (recordVertex i a) : ℝ) := by
    change (inverseMatrix *ᵥ recordRealVertex i a) j = _
    rw [inverseMatrix, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.map_apply, recordRealVertex, integerDot, Int.cast_add, Int.cast_mul]
  rw [hcoord]
  exact ⟨by linarith, by linarith⟩

private def recordIntegerShift (k : Fin 3 → ℤ) (r : Fin 3) : ℤ :=
  k 0 * recordPeriod 0 r + k 1 * recordPeriod 1 r + k 2 * recordPeriod 2 r

example : recordIntegerShift ![1, 0, 0] 2 = 192 := by decide
example : recordIntegerShift ![1, 0, 0] 2 ≠ 0 := by decide

private theorem record_integer_shift_cast (k : Fin 3 → ℤ) :
    recordCoordinates.symm (fun j => (k j : ℝ)) =
      (fun j => (recordIntegerShift k j : ℝ)) := by
  ext r
  change (periodMatrix *ᵥ (fun j => (k j : ℝ))) r = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, periodMatrix, recordIntegerShift,
    Int.cast_add, Int.cast_mul]
  ring

private theorem record_integer_separation (i j : Fin 4) (k : Fin 3 → ℤ)
    (h : i ≠ j ∨ k ≠ 0) (hk : ∀ r, -2 ≤ k r ∧ k r ≤ 2) :
    ∃ n, integerSeparates n (recordVertex i) (recordVertex j)
      (integerDot n (recordIntegerShift k)) = true := by
  let idx (r : Fin 3) : Fin 5 := ⟨(k r + 2).toNat, by have := hk r; omega⟩
  have hidx (r : Fin 3) : ((idx r).val : ℤ) - 2 = k r := by
    change ((k r + 2).toNat : ℤ) - 2 = k r
    have := hk r
    omega
  have hexc : ¬ (i = j ∧ idx 0 = 2 ∧ idx 1 = 2 ∧ idx 2 = 2) := by
    rintro ⟨heq, h₀, h₁, h₂⟩
    have hz : k = 0 := by
      ext r
      fin_cases r
      · simpa [h₀] using (hidx 0).symm
      · simpa [h₁] using (hidx 1).symm
      · simpa [h₂] using (hidx 2).symm
    exact h.elim (fun hne => hne heq) (fun hne => hne hz)
  obtain ⟨n, hn⟩ := record_integer_separator i j (idx 0) (idx 1) (idx 2) hexc
  simp only [hidx] at hn
  refine ⟨n, ?_⟩
  have hproj : integerDot n (recordIntegerShift k) =
      k 0 * integerDot n (recordPeriod 0) + k 1 * integerDot n (recordPeriod 1) +
      k 2 * integerDot n (recordPeriod 2) := by
    simp only [integerDot, recordIntegerShift]
    ring
  rwa [hproj]

theorem record_disjoint_interiors (i j : Fin 4) (k : Fin 3 → ℤ) (h : i ≠ j ∨ k ≠ 0) :
    Disjoint (interior (convexHull ℝ (range (recordRealVertex i))))
      (interior (convexHull ℝ (range (fun b =>
        recordRealVertex j b + recordCoordinates.symm (fun r => (k r : ℝ)))))) := by
  rw [record_integer_shift_cast k]
  apply integer_shift_certificates_of_box recordCoordinates recordIntegerShift
    record_integer_shift_cast
    (recordVertex i) (recordVertex j) (fun k => i ≠ j ∨ k ≠ 0)
    (fun _ => -3 / 2) (fun _ => 7 / 5) (fun _ => -3 / 2) (fun _ => 7 / 5)
    (fun _ => -2) (fun _ => 2) (record_coordinate_bounds i) (record_coordinate_bounds j)
    (fun _ => by norm_num) (fun _ => by norm_num) _ k h
  intro shift hb hs
  exact record_integer_separation i j shift hs ((mem_integerShiftBox _ _ _).mp hb)

theorem record_pairwise_disjoint_interiors :
    let piece (p : Fin 4 × (Fin 3 → ℤ)) :=
      convexHull ℝ (range (fun b =>
        recordRealVertex p.1 b + recordCoordinates.symm (fun r => (p.2 r : ℝ))))
    Pairwise fun p q => Disjoint (interior (piece p)) (interior (piece q)) := by
  dsimp only
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  have hne : i ≠ j ∨ l - k ≠ 0 := by
    by_contra! heq
    exact h (Prod.ext heq.1 (sub_eq_zero.mp heq.2).symm)
  let e := Homeomorph.addRight (recordCoordinates.symm (fun r => (k r : ℝ)))
  have hd := disjoint_image_of_injective e.injective (record_disjoint_interiors i j (l - k) hne)
  simp only [e.image_interior] at hd
  have shift_eq : (fun r : Fin 3 => (↑((l - k) r) : ℝ)) =
      (fun r => (l r : ℝ)) - (fun r => (k r : ℝ)) := by
    ext r
    exact Int.cast_sub _ _
  have translate_hull (v : Fin 4 → Fin 3 → ℝ) :
      e '' convexHull ℝ (range v) =
        convexHull ℝ (range fun b => v b + recordCoordinates.symm (fun r => (k r : ℝ))) := by
    simpa [e, ← range_comp, Function.comp_def, add_comm] using
      AffineMap.image_convexHull
        (AffineEquiv.vaddConst ℝ (recordCoordinates.symm (fun r => (k r : ℝ)))).toAffineMap
        (range v)
  rw [translate_hull, translate_hull] at hd
  simpa only [shift_eq, map_sub, add_assoc, sub_add_cancel] using hd

end TetrahedronPacking
