/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4207T1FormulaRestriction
public import LeanPool.ApollonianSuperharmonic.DiamondParameter
public import LeanPool.ApollonianSuperharmonic.P4207T1FloorArithmetic
public import LeanPool.ApollonianSuperharmonic.CurvatureOneOdometer
public import LeanPool.ApollonianSuperharmonic.OdometerTranslation
public import LeanPool.ApollonianSuperharmonic.PartialOdometerSlope
public import Mathlib.Algebra.Ring.Int.Parity

-- [TABLET NODE: P4207T1UnitRestrictions]

/-!
# P4207T1UnitRestrictions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4207T1UnitRestrictions (K : DiamondParameter) :
    let k := (K.1 : Int)
    let bases : Fin 2 → Bool → GaussianInt :=
      ![fun s => if s then ⟨-k, k - 1⟩ else ⟨k - 1, k⟩,
        fun s => if s then ⟨k - 1, k - 1⟩ else ⟨-k, k⟩]
    let slopes : Fin 2 → Bool → ℝ × ℝ :=
      ![fun s => if s then (1 / 2, 1 / 2 - (K.1 : Real)) else
          ((K.1 : Real) - 1 / 2, -1 / 2),
        fun s => if s then ((K.1 : Real) - 1, 0) else (1, -(K.1 : Real))]
    ∀ i s, OdometerTranslation
        (P4207T1FormulaRestriction ⟨{bases i s}, bases i s⟩)
        (CurvatureOneOdometer (if i = 0 then ⟨0, 1⟩ else 0)) ∧
      PartialOdometerSlope
        (P4207T1FormulaRestriction ⟨{bases i s}, bases i s⟩) =
        some (slopes i s) := by
-- BODY
  classical
  have square (u : GaussianInt) (d a b c : Int)
      (h00 : P4207T1DiamondFormula u = c)
      (h10 : P4207T1DiamondFormula (u + 1) = c + a)
      (h01 : P4207T1DiamondFormula (u + ⟨0, 1⟩) = c + b)
      (h11 : P4207T1DiamondFormula (u + 1 + ⟨0, 1⟩) = c + a + b + d) :
      OdometerTranslation (P4207T1FormulaRestriction ⟨{u}, u⟩)
          (CurvatureOneOdometer ⟨0, d⟩) ∧
        PartialOdometerSlope (P4207T1FormulaRestriction ⟨{u}, u⟩) =
          some ((a : Real) + (d : Real) / 2, (b : Real) + (d : Real) / 2) := by as_aux_lemma =>
    let h := P4207T1FormulaRestriction ⟨{u}, u⟩
    have hd : h.domain = {u, u + 1, u + ⟨0, 1⟩, u + 1 + ⟨0, 1⟩} := by
      simp [h, P4207T1FormulaRestriction]
    have value (x : GaussianInt) (hx : x ∈ h.domain) :
        h.value x = P4207T1DiamondFormula x := by
      change (if x ∈ h.domain then _ else 0) = _
      exact ite_eq_left hx
    have v00 : h.value u = c := by
      rw [value u (by simp [hd]), h00]
    have v10 : h.value (u + 1) = c + a := by
      rw [value _ (by simp [hd]), h10]
    have v01 : h.value (u + ⟨0, 1⟩) = c + b := by
      rw [value _ (by simp [hd]), h01]
    have v11 : h.value (u + 1 + ⟨0, 1⟩) = c + a + b + d := by
      rw [value _ (by simp [hd]), h11]
    have hs : PartialOdometerSquares h = {u} := by
      ext y
      simp only [PartialOdometerSquares, Finset.mem_filter, hd,
        Finset.mem_insert, Finset.mem_singleton, Zsqrtd.ext_iff,
        Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one]
      norm_num
      omega
    constructor
    · refine ⟨u, ⟨a, b⟩, c - a * u.re - b * u.im, ?_, ?_⟩
      · intro y
        change y ∈ h.domain ↔ _
        rw [hd]
        simp only [CurvatureOneOdometer, Finset.mem_insert,
          Finset.mem_singleton, Zsqrtd.ext_iff, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
          Zsqrtd.re_zero, Zsqrtd.im_zero]
        norm_num
        omega
      · intro y hy
        change h.value y = _
        change y ∈ h.domain at hy
        rw [hd] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        all_goals simp [CurvatureOneOdometer, v00, v10, v01, v11, Zsqrtd.ext_iff]
        all_goals ring
    · change PartialOdometerSlope h = _
      simp only [PartialOdometerSlope, hs, Finset.singleton_nonempty, ↓reduceIte,
        Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, v00, v10, v01, v11]
      push_cast
      congr 1; ext <;> ring
  dsimp only
  intro i s
  let n : Int := K.1
  have hn : 1 ≤ n := by have := K.2; dsimp [n]; omega
  let A : Int := n * (n - 1) / 2
  let B : Int := (n - 1) * (n - 2) / 2
  let C : Int := n * (n + 1) / 2
  have triangle (t : Int) : 2 * (t * (t - 1) / 2) = t * (t - 1) := by
    obtain ⟨r, hr⟩ := Int.even_mul_pred_self t
    omega
  have hA : 2 * A = n * (n - 1) := triangle n
  have hB : 2 * B = (n - 1) * (n - 2) := by
    have e : n - 1 - 1 = n - 2 := by ring
    simpa only [e] using triangle (n - 1)
  have hC : 2 * C = n * (n + 1) := by
    have e : (n + 1) * (n + 1 - 1) = n * (n + 1) := by ring
    simpa only [e] using triangle (n + 1)
  have hn0 : 0 ≤ n := by omega
  have hn1 : 0 ≤ n - 1 := by omega
  have hnn : -n ≤ 0 := by omega
  have hnn1 : -n + 1 ≤ 0 := by omega
  have table :
      (P4207T1DiamondFormula ⟨-n, n - 1⟩ = -A ∧
       P4207T1DiamondFormula (⟨-n, n - 1⟩ + 1) = -A ∧
       P4207T1DiamondFormula (⟨-n, n - 1⟩ + ⟨0, 1⟩) = -A - n ∧
       P4207T1DiamondFormula (⟨-n, n - 1⟩ + 1 + ⟨0, 1⟩) = -A - n + 1) ∧
      (P4207T1DiamondFormula ⟨n - 1, n⟩ = B ∧
       P4207T1DiamondFormula (⟨n - 1, n⟩ + 1) = A ∧
       P4207T1DiamondFormula (⟨n - 1, n⟩ + ⟨0, 1⟩) = B - 1 ∧
       P4207T1DiamondFormula (⟨n - 1, n⟩ + 1 + ⟨0, 1⟩) = A) ∧
      (P4207T1DiamondFormula ⟨n - 1, n - 1⟩ = B ∧
       P4207T1DiamondFormula (⟨n - 1, n - 1⟩ + 1) = A ∧
       P4207T1DiamondFormula (⟨n - 1, n - 1⟩ + ⟨0, 1⟩) = B ∧
       P4207T1DiamondFormula (⟨n - 1, n - 1⟩ + 1 + ⟨0, 1⟩) = A) ∧
      (P4207T1DiamondFormula ⟨-n, n⟩ = -C ∧
       P4207T1DiamondFormula (⟨-n, n⟩ + 1) = -C + 1 ∧
       P4207T1DiamondFormula (⟨-n, n⟩ + ⟨0, 1⟩) = -C - n ∧
       P4207T1DiamondFormula (⟨-n, n⟩ + 1 + ⟨0, 1⟩) = -C - n + 1) := by as_aux_lemma =>
    norm_num [P4207T1DiamondFormula, Int.natCast_natAbs,
      abs_of_nonneg hn0, abs_of_nonneg hn1, abs_of_nonpos hnn,
      abs_of_nonpos hnn1, neg_neg]
    dsimp only [A, B, C] at hA hB hC ⊢
    ring_nf at hA hB hC ⊢
    generalize hsquare : n ^ 2 = p at hA hB hC ⊢
    norm_num at hA hB hC ⊢
    omega
  have hBA : A - B = n - 1 := by nlinarith only [hA, hB]
  fin_cases i <;> cases s
  · have row := table.2.1
    have hs := square ⟨n - 1, n⟩ 1 (n - 1) (-1) B row.1
      (by rw [row.2.1]; omega) (by rw [row.2.2.1]; ring)
      (by rw [row.2.2.2]; omega)
    convert hs using 1 <;> simp [n]; ring
  · have row := table.1
    have hs := square ⟨-n, n - 1⟩ 1 0 (-n) (-A) row.1
      (by rw [row.2.1]; ring) (by rw [row.2.2.1]; ring)
      (by rw [row.2.2.2]; ring)
    convert hs using 1 <;> simp [n]; ring
  · have row := table.2.2.2
    have hs := square ⟨-n, n⟩ 0 1 (-n) (-C) row.1
      (by rw [row.2.1] ) (by simpa only [sub_eq_add_neg] using row.2.2.1)
      (by rw [row.2.2.2]; ring)
    convert hs using 1 <;> simp [n, show (⟨0, 0⟩ : GaussianInt) = 0 from rfl]
  · have row := table.2.2.1
    have hs := square ⟨n - 1, n - 1⟩ 0 (n - 1) 0 B row.1
      (by rw [row.2.1]; omega) (by rw [row.2.2.1]; ring)
      (by rw [row.2.2.2]; omega)
    convert hs using 1 <;>
      simp [n, show (⟨0, 0⟩ : GaussianInt) = 0 from rfl]

end ApollonianSuperharmonic

end
