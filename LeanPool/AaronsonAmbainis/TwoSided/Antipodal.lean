/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.TwoSided.Basic

/-!
# The antipodal inequality from the determinant inequality (`antipodal_of_det`)

The pointwise step (Lemma 4.2 of the paper) and the proof of the antipodal inequality
(Theorem 4.3) from the determinant inequality (Corollary 3.2).

With `ℓ j = 1 / w j`, `x = lam u`, `y = lam (antipode u)`, `S = ∑ j, w j * x j * y j` and
`D = S⁻¹` (Lean: `0⁻¹ = 0`), the wing at `u` is `wingSet w x y`: empty if `S = 0`, and
`{j : ℓ j < D * y j}` otherwise.  (By the overlap lemma, Lemma 4.1 of the paper, `S > 0` on the
zone; the case `S = 0` is treated directly here, so that the overlap lemma is not needed in this
file.)
-/

@[expose] public section

namespace AaronsonAmbainis

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Steps 1 and 2 of the proof of Lemma 4.2 of the paper: if `x` is a row at `u`, `g u = true`
and `S = ∑ j, w j * x j * y j > 0`, then `{j : 1 / w j < S⁻¹ * y j}` is a 1-wing at `u`. -/
lemma wing_of_row {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j)
    (hpos : 0 < ∑ j, w j * x j * y j) :
    IsWing g u (univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j) := by
  intro T hT
  by_contra hne
  have hne' : g (flipSet u T) ≠ g u := by rw [hu]; exact hne
  have h1 : 1 ≤ ∑ j ∈ T, x j := hx.2 T hne'
  set Sm := ∑ j, w j * x j * y j with hSm
  have hD : 0 < Sm⁻¹ := inv_pos.mpr hpos
  -- every `j ∈ T` has `1 < w j * (Sm⁻¹ * y j)`
  have hA : ∀ j ∈ T, 1 < w j * (Sm⁻¹ * y j) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp (hT hj)).2
    have h2 := mul_lt_mul_of_pos_left hj' (hw j)
    rwa [mul_inv_cancel₀ (hw j).ne'] at h2
  have hle : ∀ j ∈ T, x j ≤ x j * (w j * (Sm⁻¹ * y j)) := by
    intro j hj
    have h3 := hA j hj
    nlinarith [hx.1 j]
  obtain ⟨j0, hj0T, hj0⟩ : ∃ j ∈ T, 0 < x j := by
    by_contra hcon
    have h4 : ∑ j ∈ T, x j ≤ 0 :=
      Finset.sum_nonpos fun j hj => not_lt.mp fun hp => hcon ⟨j, hj, hp⟩
    linarith
  have hlt : ∑ j ∈ T, x j < ∑ j ∈ T, x j * (w j * (Sm⁻¹ * y j)) := by
    apply Finset.sum_lt_sum hle
    refine ⟨j0, hj0T, ?_⟩
    have h5 := hA j0 hj0T
    nlinarith
  have hsub : ∑ j ∈ T, x j * (w j * (Sm⁻¹ * y j)) ≤ ∑ j, x j * (w j * (Sm⁻¹ * y j)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    intro j _ _
    exact mul_nonneg (hx.1 j) (mul_nonneg (hw j).le (mul_nonneg hD.le (hy j)))
  have htot : ∑ j, x j * (w j * (Sm⁻¹ * y j)) = 1 := by
    have h6 : ∑ j, x j * (w j * (Sm⁻¹ * y j)) = Sm⁻¹ * Sm := by
      rw [hSm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h6, inv_mul_cancel₀ hpos.ne']
  linarith

omit [Fintype ι] in
/-- Step 3 of the proof of Lemma 4.2 of the paper: if `y` is a row at `u'`, `g u' = false`,
`g (u'^G) = true` and `D * y j ≤ ℓ j` on `G`, then `D ≤ ℓ(G)`. -/
lemma lower_of_row {g : Cube ι → Bool} {u' : Cube ι} {y ℓ : ι → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hy : IsRow g u' y) (hu' : g u' = false) (G : Finset ι)
    (hG : ∀ j ∈ G, D * y j ≤ ℓ j) (hgG : g (flipSet u' G) = true) :
    D ≤ ∑ j ∈ G, ℓ j := by
  have hne : g (flipSet u' G) ≠ g u' := by rw [hgG, hu']; simp
  have h1 : 1 ≤ ∑ j ∈ G, y j := hy.2 G hne
  calc D = D * 1 := (mul_one D).symm
    _ ≤ D * ∑ j ∈ G, y j := mul_le_mul_of_nonneg_left h1 hD
    _ = ∑ j ∈ G, D * y j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ G, ℓ j := Finset.sum_le_sum hG

/-- The wing used at a point with rows `x` (at the point) and `y` (at its antipode). -/
noncomputable def wingSet (w x y : ι → ℝ) : Finset ι :=
  if ∑ j, w j * x j * y j = 0 then ∅
  else univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j

lemma wingSet_isWing {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j) :
    IsWing g u (wingSet w x y) := by
  unfold wingSet
  split_ifs with h0
  · intro S hS
    rw [Finset.subset_empty.mp hS, flipSet_empty]
    exact hu
  · have hnn : 0 ≤ ∑ j, w j * x j * y j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hx.1 j)) (hy j)
    exact wing_of_row hu hw hx hy (lt_of_le_of_ne hnn (Ne.symm h0))

lemma wingSet_lower {g : Cube ι → Bool} {u' : Cube ι} {x y w : ι → ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 ≤ x j) (hy : IsRow g u' y) (hu' : g u' = false)
    (G : Finset ι) (hG : Disjoint G (wingSet w x y)) (hgG : g (flipSet u' G) = true) :
    (∑ j, w j * x j * y j)⁻¹ ≤ ∑ j ∈ G, (w j)⁻¹ := by
  have hnn : 0 ≤ ∑ j, w j * x j * y j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw j).le (hx j)) (hy.1 j)
  by_cases h0 : ∑ j, w j * x j * y j = 0
  · rw [h0, inv_zero]
    exact Finset.sum_nonneg fun j _ => (inv_pos.mpr (hw j)).le
  · unfold wingSet at hG
    rw [ite_eq_right h0] at hG
    refine lower_of_row (inv_nonneg.mpr hnn) hy hu' G ?_ hgG
    intro j hj
    have hjA := Finset.disjoint_left.mp hG hj
    exact not_lt.mp fun hlt => hjA (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩)

/-- The antipodal inequality (the inequality of Theorem 4.3 of the paper) from the determinant
inequality (Corollary 3.2). -/
theorem antipodal_of_det : DetInequality → AntipodalInequality := by
  intro hDet ι _ _ g w hw lam hlam
  have key := hDet ι g (fun j => (w j)⁻¹) (fun j => inv_pos.mpr (hw j))
    (fun u => wingSet w (lam u) (lam (antipode u)))
    (fun u hu => wingSet_isWing (mem_zone.mp hu).1 hw (hlam u) (hlam (antipode u)).1)
    (fun u => (∑ j, w j * lam u j * lam (antipode u) j)⁻¹)
    (fun u hu G hG hgG =>
      wingSet_lower hw (hlam u).1 (hlam (antipode u)) (mem_zone.mp hu).2 G hG hgG)
  calc ∑ u ∈ zone g, (∑ j, w j * lam u j * lam (antipode u) j)⁻¹
      ≤ ∑ j, (w j)⁻¹ * (bdry g j : ℝ) := key
    _ = ∑ j, (bdry g j : ℝ) / w j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [div_eq_mul_inv, mul_comm]

end AaronsonAmbainis
