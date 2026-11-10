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

/-- **The Horner-tail combination of the linear-factor columns**: summing the columns of the
`q·(w+X)`-pattern matrix against the Horner tails of `A` produces the moment-system row value
minus `A(-w)` times the plain first column. This is the column operation behind the value
identity `det M·A(-w) = ±s_Λ(T ∪ {w})`. -/
theorem horner_col_sum {n : ℕ} {A : R[X]} (hA : A.natDegree ≤ n) (w : R) (k : ℕ) :
    ∑ m : Fin n, (∑ l ∈ Finset.range (n - (m : ℕ)), A.coeff ((m : ℕ) + 1 + l) * (-w) ^ l)
        * (q * (C w + X) * X ^ (m : ℕ)).coeff k
      = (A * q).coeff k - A.eval (-w) * q.coeff k := by
  have hH : ∀ m : ℕ, (fun m ↦ ∑ l ∈ Finset.range (n - m), A.coeff (m + 1 + l) * (-w) ^ l) m
      = ∑ l ∈ Finset.range (n - m), A.coeff (m + 1 + l) * (-w) ^ l := fun m ↦ rfl
  set H : ℕ → R := fun m ↦ ∑ l ∈ Finset.range (n - m), A.coeff (m + 1 + l) * (-w) ^ l
  -- the Horner recursion and the two boundary identities
  have hHrec : ∀ j < n, H j = A.coeff (j + 1) + -w * H (j + 1) := by
    intro j hj
    simp only [hH]
    rw [show n - j = (n - (j + 1)) + 1 by lia, Finset.sum_range_succ',
      Finset.sum_congr rfl (fun l _ ↦ show A.coeff (j + 1 + (l + 1)) * (-w) ^ (l + 1)
        = -w * (A.coeff (j + 1 + 1 + l) * (-w) ^ l) by
          rw [show j + 1 + (l + 1) = j + 1 + 1 + l by lia, pow_succ]
          ring),
      ← Finset.mul_sum, add_zero, pow_zero, mul_one, add_comm]
  have hHtop : 1 ≤ n → H (n - 1) = A.coeff n := by
    intro h0
    simp only [hH]
    rw [show n - (n - 1) = 1 by lia, Finset.sum_range_one, pow_zero, mul_one,
      show n - 1 + 1 + 0 = n by lia]
  have hev : A.eval (-w) = A.coeff 0 + -w * H 0 := by
    simp only [hH, Nat.sub_zero]
    rw [eval_eq_sum_range' (n := n + 1) (by lia),
      Finset.sum_range_succ',
      Finset.sum_congr rfl (fun l _ ↦ show A.coeff (l + 1) * (-w) ^ (l + 1)
        = -w * (A.coeff (0 + 1 + l) * (-w) ^ l) by
          rw [pow_succ, show (0 : ℕ) + 1 + l = l + 1 by lia]
          ring),
      ← Finset.mul_sum, pow_zero, mul_one, add_comm]
  -- convert to a range sum of split columns
  have h1 : ∑ m : Fin n, H (m : ℕ) * (q * (C w + X) * X ^ (m : ℕ)).coeff k
      = ∑ m : Fin n, (w * H (m : ℕ) * (q * X ^ (m : ℕ)).coeff k
          + H (m : ℕ) * (q * X ^ ((m : ℕ) + 1)).coeff k) :=
    Finset.sum_congr rfl fun m _ ↦ by rw [coeff_mul_linear]; ring
  have h2 : ∑ m : Fin n, (w * H (m : ℕ) * (q * X ^ (m : ℕ)).coeff k
        + H (m : ℕ) * (q * X ^ ((m : ℕ) + 1)).coeff k)
      = ∑ m ∈ Finset.range n, (w * H m * (q * X ^ m).coeff k
          + H m * (q * X ^ (m + 1)).coeff k) :=
    Fin.sum_univ_eq_sum_range
      (fun m ↦ w * H m * (q * X ^ m).coeff k + H m * (q * X ^ (m + 1)).coeff k) n
  rw [h1, h2]
  -- telescoping: the partial sums absorb the Horner recursion
  have hpart : ∀ j, 1 ≤ j → j ≤ n →
      ∑ m ∈ Finset.range j, (w * H m * (q * X ^ m).coeff k
          + H m * (q * X ^ (m + 1)).coeff k)
        = w * H 0 * (q * X ^ 0).coeff k - A.coeff 0 * (q * X ^ 0).coeff k
          + ∑ m ∈ Finset.range j, A.coeff m * (q * X ^ m).coeff k
          + H (j - 1) * (q * X ^ j).coeff k := by
    intro j hj1 hjn
    induction j with
    | zero => lia
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [Finset.sum_range_one, Finset.sum_range_one]
        norm_num
      · have hrec := hHrec (j - 1) (by lia)
        rw [show j - 1 + 1 = j by lia] at hrec
        have h3 : ∑ m ∈ Finset.range (j + 1), A.coeff m * (q * X ^ m).coeff k
            = ∑ m ∈ Finset.range j, A.coeff m * (q * X ^ m).coeff k
              + A.coeff j * (q * X ^ j).coeff k :=
          Finset.sum_range_succ (fun m ↦ A.coeff m * (q * X ^ m).coeff k) j
        rw [Finset.sum_range_succ, ih hj0 (by lia), h3, Nat.add_sub_cancel]
        linear_combination ((q * X ^ j).coeff k) * hrec
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- constant `A`: both sides collapse
    rw [Finset.sum_range_zero, Polynomial.eq_C_of_natDegree_le_zero hA, coeff_C_mul, eval_C]
    ring
  · rw [hpart n hn le_rfl, hHtop hn,
      coeff_mul_eq_sum_coeff_mul_X_pow (q := q) (g := n) hA k, Finset.sum_range_succ]
    have hq0 : (q * X ^ 0).coeff k = q.coeff k := by rw [pow_zero, mul_one]
    rw [hq0]
    linear_combination (q.coeff k) * hev

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
