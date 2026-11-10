/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.MomentDet

/-!
# The value identity: fold conditions are pattern determinants

This file proves the determinant form of `thm:cusp-moment` (3): for a monic solution `A` of
the moment system of a node polynomial value `q`, adjoining a linear factor computes a value
of `A`,
`momentDet (q·(w+X)) id = ±A(-w)·det M` (`ChabautyColeman.momentDet_linear`). Consequently
every fold condition — a value of the reduced support at `±t` or `0` — is, up to the moment
determinant, a **single** pattern determinant of an extended alphabet, which is the exact
shape the peeling certificates attack.

The proof is a column operation and the first survivor analysis of the peel framework: adding
the Horner-tail combination of all columns to the last one turns it into `-A(-w)` times the
plain first column (`ChabautyColeman.horner_col_sum`, using the moment system), and the
resulting determinant has a single surviving choice in the peel expansion — the full cyclic
shift, whose sign is `Equiv.Perm.sign (finRotate _)`
(`ChabautyColeman.det_updateCol_last_linear`, `ChabautyColeman.momentDet_rotate`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Bridge

variable {R : Type*} [CommRing R] {g : ℕ} {q A : R[X]} {w : R}

/-- One column of the linear-factor pattern matrix, in terms of the plain columns. -/
theorem coeff_mul_linear (q : R[X]) (w : R) (s k : ℕ) :
    (q * (C w + X) * X ^ s).coeff k
      = w * (q * X ^ s).coeff k + (q * X ^ (s + 1)).coeff k := by
  have h2 : q * (C w + X) * X ^ s = C w * (q * X ^ s) + q * X ^ (s + 1) := by
    rw [pow_succ]
    ring
  rw [h2, coeff_add, coeff_C_mul]

/-- A bounded Horner tail is a coefficient of division by a monic linear factor. -/
private theorem coeff_divByMonic_X_sub_C_range {A : R[X]} {n : ℕ} (hA : A.natDegree ≤ n)
    (a : R) (m : ℕ) :
    (A /ₘ (X - C a)).coeff m =
      ∑ l ∈ Finset.range (n - m), A.coeff (m + 1 + l) * a ^ l := by
  rw [coeff_divByMonic_X_sub_C]
  calc
    ∑ i ∈ Finset.Icc (m + 1) A.natDegree, a ^ (i - (m + 1)) * A.coeff i
        = ∑ i ∈ Finset.Icc (m + 1) n, a ^ (i - (m + 1)) * A.coeff i := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc_right hA)
      intro i hi hnot
      have hdeg : A.natDegree < i := by
        have hi₁ := (Finset.mem_Icc.mp hi).1
        simp only [Finset.mem_Icc, not_and, not_le] at hnot
        exact hnot hi₁
      rw [coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
    _ = _ := by
      rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      change (∑ k ∈ Finset.range ((n + 1) - (m + 1)),
        a ^ (m + 1 + k - (m + 1)) * A.coeff (m + 1 + k)) = _
      simp only [Nat.add_sub_add_right, Nat.add_sub_cancel_left, mul_comm]

/-- **The Horner-tail combination of the linear-factor columns**: summing the columns of the
`q·(w+X)`-pattern matrix against the Horner tails of `A` produces the moment-system row value
minus `A(-w)` times the plain first column. This is the column operation behind the value
identity `det M·A(-w) = ±s_Λ(T ∪ {w})`. -/
theorem horner_col_sum {n : ℕ} {A : R[X]} (hA : A.natDegree ≤ n) (w : R) (k : ℕ) :
    ∑ m : Fin n, (∑ l ∈ Finset.range (n - (m : ℕ)), A.coeff ((m : ℕ) + 1 + l) * (-w) ^ l)
        * (q * (C w + X) * X ^ (m : ℕ)).coeff k
      = (A * q).coeff k - A.eval (-w) * q.coeff k := by
  classical
  nontriviality R
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Polynomial.eq_C_of_natDegree_le_zero hA]
    simp
  let B := A /ₘ (X - C (-w))
  have hBdeg : B.natDegree < n := by
    dsimp only [B]
    rw [natDegree_divByMonic A (monic_X_sub_C _), natDegree_X_sub_C]
    lia
  have hB : B = ∑ m : Fin n, C (B.coeff m) * X ^ (m : ℕ) := by
    exact (B.as_sum_range_C_mul_X_pow' hBdeg).trans
      (Fin.sum_univ_eq_sum_range (fun m : ℕ ↦ C (B.coeff m) * X ^ m) n).symm
  have hfac : B * (C w + X) = A - C (A.eval (-w)) := by
    have h := A.modByMonic_add_div (X - C (-w))
    rw [modByMonic_X_sub_C_eq_C_eval, map_neg, sub_neg_eq_add] at h
    dsimp only [B]
    rw [map_neg, sub_neg_eq_add]
    linear_combination h
  calc
    _ = ∑ m : Fin n, ((C (B.coeff m) * X ^ (m : ℕ)) * (q * (C w + X))).coeff k := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← coeff_divByMonic_X_sub_C_range hA (-w)]
      change B.coeff m * _ = _
      rw [show C (B.coeff m) * X ^ (m : ℕ) * (q * (C w + X)) =
        C (B.coeff m) * (q * (C w + X) * X ^ (m : ℕ)) by ring, coeff_C_mul]
    _ = (B * (q * (C w + X))).coeff k := by
      rw [← finsetSum_coeff, ← Finset.sum_mul, ← hB]
    _ = _ := by
      rw [show B * (q * (C w + X)) = (B * (C w + X)) * q by ring,
        hfac, sub_mul, coeff_sub, coeff_C_mul]

/-- The cyclically rotated pattern is the moment determinant, up to the sign of the cycle. -/
theorem momentDet_rotate (g : ℕ) (q : R[X]) :
    momentDet (g + 1) q (fun m ↦ if m = Fin.last g then 0 else (m : ℕ) + 1)
      = (-1) ^ g * (momentMatrix (g + 1) q).det := by
  have h1 : (Matrix.of fun i m : Fin (g + 1) ↦
      (q * X ^ (if m = Fin.last g then 0 else (m : ℕ) + 1)).coeff (2 * (i : ℕ) + 1))
      = (momentMatrix (g + 1) q).submatrix id (finRotate (g + 1)) := by
    ext i m
    rw [Matrix.submatrix_apply, id_eq, finRotate_apply, momentMatrix_apply, Fin.val_add_one]
    rfl
  rw [momentDet, h1, Matrix.det_permute', sign_finRotate]
  push_cast
  ring

/-- **The cyclic survivor computation**: replacing the last column of the linear-factor
pattern matrix by the plain column `γ_0` leaves a single surviving choice in the peel
expansion — the full cyclic shift — so the determinant is `(-1)^g` times the moment
determinant. This is the prototype survivor analysis of the certificate route. -/
theorem det_updateCol_last_linear (w : R) (q : R[X]) (g : ℕ) :
    ((Matrix.of fun i m : Fin (g + 1) ↦
        (q * (C w + X) * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1)).updateCol (Fin.last g)
      (fun i ↦ q.coeff (2 * (i : ℕ) + 1))).det
      = (-1) ^ g * (momentMatrix (g + 1) q).det := by
  -- the updated matrix has columns `w·γ_m + γ_(m+1)` away from the last, and `γ_0` there
  have hcols : ((Matrix.of fun i m : Fin (g + 1) ↦
        (q * (C w + X) * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1)).updateCol (Fin.last g)
      (fun i ↦ q.coeff (2 * (i : ℕ) + 1)))
      = Matrix.of fun i m : Fin (g + 1) ↦
          ∑ r : Fin 2, (if m = Fin.last g then (if r = 0 then 1 else 0)
              else (if r = 0 then w else 1))
            * (q * X ^ (if m = Fin.last g then 0 else (m : ℕ) + (r : ℕ))).coeff
              (2 * (i : ℕ) + 1) := by
    ext i m
    rcases eq_or_ne m (Fin.last g) with rfl | hm
    · simp [Fin.sum_univ_two]
    · have h1 := coeff_mul_linear q w (m : ℕ) (2 * (i : ℕ) + 1)
      simp [hm, Fin.sum_univ_two, h1]
  rw [hcols, momentDet_expand
    (fun m r ↦ if m = Fin.last g then (if r = 0 then 1 else 0) else (if r = 0 then w else 1))
    (fun m r ↦ if m = Fin.last g then 0 else (m : ℕ) + (r : ℕ))]
  -- a single choice survives: the full cyclic shift
  rw [Finset.sum_eq_single (fun m ↦ if m = Fin.last g then 0 else 1)]
  · -- the surviving term is the rotated moment matrix
    have hprod : ∏ m : Fin (g + 1),
        (if m = Fin.last g
          then (if (if m = Fin.last g then (0 : Fin 2) else 1) = 0 then (1 : R) else 0)
          else (if (if m = Fin.last g then (0 : Fin 2) else 1) = 0 then w else 1)) = 1 :=
      Finset.prod_eq_one fun m _ ↦ by
        rcases eq_or_ne m (Fin.last g) with rfl | hm
        · simp
        · simp [hm]
    rw [hprod, one_mul, show (fun m : Fin (g + 1) ↦ if m = Fin.last g then 0
        else (m : ℕ) + (((if m = Fin.last g then (0 : Fin 2) else 1) : Fin 2) : ℕ))
        = fun m : Fin (g + 1) ↦ if m = Fin.last g then 0 else (m : ℕ) + 1 from
      funext fun m ↦ by rcases eq_or_ne m (Fin.last g) with rfl | hm <;> simp [*]]
    exact momentDet_rotate g q
  · -- every other choice dies: a zero weight or a repeated column
    intro σ _ hσ
    rcases eq_or_ne (σ (Fin.last g)) 0 with h0 | h0
    · -- σ agrees at the last column, so it differs at an interior one, where it chooses `0`
      have hne : ∃ m, m ≠ Fin.last g ∧ σ m = 0 := by
        by_contra! hc
        refine hσ (funext fun m ↦ ?_)
        rcases eq_or_ne m (Fin.last g) with rfl | hm
        · simp [h0]
        · rw [ite_eq_right hm]
          exact Fin.eq_one_of_ne_zero _ (hc m hm)
      -- the least interior zero collides with its predecessor (or with the last column)
      obtain ⟨m₀, hm₀mem, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun m ↦ m ≠ Fin.last g ∧ σ m = 0) id
        (by obtain ⟨m, hm⟩ := hne; exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩)
      obtain ⟨-, hm₀ne, hσ0⟩ := Finset.mem_filter.mp hm₀mem
      refine mul_eq_zero_of_right _ ?_
      rcases Nat.eq_zero_or_eq_succ_pred (m₀ : ℕ) with h00 | h00
      · -- the zero column collides with the last one
        refine momentDet_eq_zero_of_eq (m := m₀) (m' := Fin.last g) ?_ hm₀ne
        rw [ite_eq_right hm₀ne, ite_eq_left rfl, hσ0, h00]
        rfl
      · -- the zero column collides with its predecessor, which chose the shift
        have hlt : (m₀ : ℕ) - 1 < g + 1 := by lia
        set m₁ : Fin (g + 1) := ⟨(m₀ : ℕ) - 1, hlt⟩ with hm₁def
        have hm₁lt : m₁ < m₀ := by
          rw [Fin.lt_def]
          simp only [hm₁def]
          lia
        have hm₁ne : m₁ ≠ Fin.last g := by
          have h2 : (m₀ : ℕ) < g := by
            rcases Fin.lt_or_eq_of_le (Fin.le_last m₀) with h | h
            · rw [Fin.lt_def, Fin.val_last] at h; lia
            · exact absurd h hm₀ne
          intro hc
          rw [Fin.ext_iff, hm₁def, Fin.val_last] at hc
          simp at hc
          lia
        have hσ1 : σ m₁ = 1 := by
          refine Fin.eq_one_of_ne_zero _ fun hc ↦ ?_
          have h3 := hmin m₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm₁ne, hc⟩)
          rw [id_eq, id_eq] at h3
          exact (h3.trans_lt hm₁lt).false
        refine momentDet_eq_zero_of_eq (m := m₁) (m' := m₀) ?_ (Fin.ne_of_lt hm₁lt)
        rw [ite_eq_right hm₁ne, ite_eq_right hm₀ne, hσ0, hσ1]
        simp only [hm₁def]
        lia
    · -- the last column's weight vanishes
      refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ (Fin.last g)) ?_) _
      simp [h0]
  · exact fun h ↦ absurd (Finset.mem_univ _) h

/-- **The value identity of the moment route** (`thm:cusp-moment` (3), determinant form):
for a monic degree-`g+1` solution `A` of the moment system of `q`, the extended-alphabet
pattern determinant is `±det M·A(-w)` — so every fold condition, being a value of the
reduced support, is a single pattern determinant of an extended alphabet. -/
theorem momentDet_linear {g : ℕ} {q A : R[X]} (hA : A.Monic) (hAdeg : A.natDegree = g + 1)
    (hsys : ∀ i : Fin (g + 1), (A * q).coeff (2 * (i : ℕ) + 1) = 0) (w : R) :
    momentDet (g + 1) (q * (C w + X)) (fun m ↦ (m : ℕ))
      = (-1) ^ (g + 1) * (A.eval (-w) * (momentMatrix (g + 1) q).det) := by
  have hcg : A.coeff (g + 1) = 1 := hAdeg ▸ hA.coeff_natDegree
  -- add the Horner combination of all columns to the last one
  have h1 := Matrix.det_updateCol_sum (Matrix.of fun i m : Fin (g + 1) ↦
      (q * (C w + X) * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1)) (Fin.last g)
    (fun m ↦ ∑ l ∈ Finset.range (g + 1 - (m : ℕ)), A.coeff ((m : ℕ) + 1 + l) * (-w) ^ l)
  -- the combination column is `-A(-w)` times the plain first column
  have h2 : (fun i : Fin (g + 1) ↦ ∑ m : Fin (g + 1),
      (∑ l ∈ Finset.range (g + 1 - (m : ℕ)), A.coeff ((m : ℕ) + 1 + l) * (-w) ^ l)
        • (Matrix.of fun i m : Fin (g + 1) ↦
          (q * (C w + X) * X ^ (m : ℕ)).coeff (2 * (i : ℕ) + 1)) i m)
      = -(A.eval (-w)) • (fun i : Fin (g + 1) ↦ q.coeff (2 * (i : ℕ) + 1)) := by
    funext i
    simp only [smul_eq_mul, Matrix.of_apply, Pi.smul_apply]
    rw [horner_col_sum hAdeg.le w (2 * (i : ℕ) + 1), hsys i, zero_sub, neg_mul]
  rw [h2, Matrix.det_updateCol_smul, det_updateCol_last_linear, Fin.val_last,
    show g + 1 - g = 1 by lia, Finset.sum_range_one, pow_zero, mul_one,
    show g + 1 + 0 = g + 1 by lia, hcg, one_smul] at h1
  rw [momentDet, ← h1]
  ring

end Bridge

end ChabautyColeman

end
