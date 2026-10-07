/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedSchwartzMollifierCoordinateBound

/-!
# Coordinate expansion on the Fourier spatial carrier

Finite coordinate derivative estimates control multilinear derivatives
with complex vector values.
-/

public section

open MeasureTheory
open scoped ENNReal SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private theorem regularisedSchwartzCoordinateDirection_sum (v : L2Vec3) :
    v = ∑ i : Fin 3,
      (WithLp.ofLp v i) • regularisedSchwartzCoordinateDirection i := by
  have h := CKN.sum_smul_basisVec (WithLp.ofLp v)
  have h' := congrArg (WithLp.toLp 2) h.symm
  simpa only [WithLp.toLp_ofLp, WithLp.toLp_sum,
    WithLp.toLp_smul, regularisedSchwartzCoordinateDirection] using h'

/-- A complex vector-valued multilinear map on the Fourier spatial
carrier is controlled by its finitely many coordinate evaluations. -/
theorem regularisedComplexMultilinear_norm_le_coordinateBound
    {n : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => L2Vec3) ComplexVec3)
    (B : ℝ) (hB : 0 ≤ B)
    (hcoord : ∀ w : Fin n → Fin 3,
      ‖T (fun k => regularisedSchwartzCoordinateDirection (w k))‖ ≤ B) :
    ‖T‖ ≤ (Fintype.card (Fin n → Fin 3) : ℝ) * B := by
  classical
  have hExpand (m : Fin n → L2Vec3) :
      T m = ∑ w : Fin n → Fin 3,
        (∏ k, WithLp.ofLp (m k) (w k)) •
          T (fun k => regularisedSchwartzCoordinateDirection (w k)) := by
    calc
      T m = T (fun k => ∑ j : Fin 3,
          WithLp.ofLp (m k) j • regularisedSchwartzCoordinateDirection j) := by
        congr 1
        funext k
        exact regularisedSchwartzCoordinateDirection_sum (m k)
      _ = ∑ w : Fin n → Fin 3,
          T (fun k => WithLp.ofLp (m k) (w k) •
            regularisedSchwartzCoordinateDirection (w k)) :=
        T.toMultilinearMap.map_sum _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w _
        change T.toMultilinearMap
          (fun k => WithLp.ofLp (m k) (w k) •
            regularisedSchwartzCoordinateDirection (w k)) =
          (∏ k, WithLp.ofLp (m k) (w k)) •
            T.toMultilinearMap (fun k => regularisedSchwartzCoordinateDirection (w k))
        exact T.toMultilinearMap.map_smul_univ
          (fun k => WithLp.ofLp (m k) (w k))
          (fun k => regularisedSchwartzCoordinateDirection (w k))
  have hCoef (m : Fin n → L2Vec3) (w : Fin n → Fin 3) :
      |∏ k, WithLp.ofLp (m k) (w k)| ≤ ∏ k, ‖m k‖ := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    intro k _
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le (m k) (w k)
  have hTerm (m : Fin n → L2Vec3) (w : Fin n → Fin 3) :
      ‖(∏ k, WithLp.ofLp (m k) (w k)) •
        T (fun k => regularisedSchwartzCoordinateDirection (w k))‖ ≤
          B * ∏ k, ‖m k‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |∏ k, WithLp.ofLp (m k) (w k)| *
          ‖T (fun k => regularisedSchwartzCoordinateDirection (w k))‖ ≤
        (∏ k, ‖m k‖) * B :=
          (mul_le_mul_of_nonneg_right (hCoef m w) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left (hcoord w)
              (Finset.prod_nonneg fun k _ => norm_nonneg _))
      _ = B * ∏ k, ‖m k‖ := mul_comm _ _
  have hBound (m : Fin n → L2Vec3) :
      ‖T m‖ ≤ (Fintype.card (Fin n → Fin 3) : ℝ) * B *
        ∏ k, ‖m k‖ := by
    rw [hExpand]
    calc
      ‖∑ w : Fin n → Fin 3,
          (∏ k, WithLp.ofLp (m k) (w k)) •
            T (fun k => regularisedSchwartzCoordinateDirection (w k))‖ ≤
        ∑ w : Fin n → Fin 3,
          ‖(∏ k, WithLp.ofLp (m k) (w k)) •
            T (fun k => regularisedSchwartzCoordinateDirection (w k))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _w : Fin n → Fin 3, B * ∏ k, ‖m k‖ :=
        Finset.sum_le_sum fun w _ => hTerm m w
      _ = (Fintype.card (Fin n → Fin 3) : ℝ) * B *
          ∏ k, ‖m k‖ := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  exact ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (Nat.cast_nonneg _) hB) hBound


end CKN.Leray

end
