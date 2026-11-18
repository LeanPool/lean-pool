/-
Copyright (c) 2026 Marcel Blattner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Blattner
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import LeanPool.CorlessNilpotent.Main

/-!
# From Corless's matrices to the matching polynomial

`T m u` is the `m × m` skew-symmetric tridiagonal matrix with zero diagonal, superdiagonal `u` and
subdiagonal `-u`. Its characteristic polynomial is obtained from `Dv s m`, `s = u²`, by substituting
`x = λ²` and reflecting, so `T m u` is nilpotent exactly when `Dv s m = 1`.
-/

@[expose] public section

open Polynomial Matrix

namespace Corless

/-- Corless's matrix: zero diagonal, superdiagonal `u`, subdiagonal `-u`. -/
def T (m : ℕ) (u : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if (j : ℕ) = i + 1 then u i else if (i : ℕ) = j + 1 then -u j else 0

/-- The characteristic matrix of `T m u`, written out. -/
noncomputable def CM (m : ℕ) (u : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  fun i j => if i = j then X else if (j : ℕ) = i + 1 then -C (u i)
    else if (i : ℕ) = j + 1 then C (u j) else 0

lemma charmatrix_T (m : ℕ) (u : ℕ → ℂ) : charmatrix (T m u) = CM m u := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [CM, T]
  · rw [charmatrix_apply_ne _ _ _ h]
    simp only [CM, T, h, ite_false]
    split_ifs <;> simp

lemma det_CM_one (u : ℕ → ℂ) : (CM 1 u).det = X := by
  rw [Matrix.det_unique]
  simp [CM]

/-- Expansion along the first column, then along the first row of the second minor. -/
lemma det_CM_succ_succ (m : ℕ) (u : ℕ → ℂ) :
    (CM (m + 2) u).det = X * (CM (m + 1) (fun i => u (i + 1))).det
      + C (u 0 ^ 2) * (CM m (fun i => u (i + 2))).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  -- terms with row index ≥ 2 vanish: column 0 has entries only in rows 0 and 1
  have hrest : ∑ i : Fin m, (-1 : ℂ[X]) ^ ((i.succ.succ : Fin (m + 2)) : ℕ)
      * CM (m + 2) u i.succ.succ 0
      * ((CM (m + 2) u).submatrix (i.succ.succ).succAbove Fin.succ).det = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have h1 : CM (m + 2) u i.succ.succ 0 = 0 := by
      simp [CM, Fin.ext_iff, Fin.val_succ]
    rw [h1, mul_zero, zero_mul]
  rw [hrest, add_zero]
  -- first minor: rows and columns 1, …, m+1
  have hA : (CM (m + 2) u).submatrix (Fin.succAbove (0 : Fin (m + 2))) Fin.succ
      = CM (m + 1) (fun i => u (i + 1)) := by
    ext i j
    simp [CM, Fin.ext_iff, Fin.val_succ]
  -- second minor: rows 0, 2, …, m+1 and columns 1, …, m+1; its first row is (-u 0, 0, …, 0)
  have hB : ((CM (m + 2) u).submatrix (Fin.succAbove (Fin.succ (0 : Fin (m + 1)))) Fin.succ).det
      = -C (u 0) * (CM m (fun i => u (i + 2))).det := by
    rw [Fin.succ_zero_eq_one, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hrest' : ∑ j : Fin m, (-1 : ℂ[X]) ^ ((j.succ : Fin (m + 1)) : ℕ)
        * (CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ 0 j.succ
        * (((CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ).submatrix Fin.succ
            (j.succ).succAbove).det = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have h1 :
          (CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ 0 j.succ = 0 := by
        simp only [submatrix_apply, CM]
        have e0 : (Fin.succAbove (1 : Fin (m + 2))) 0 = 0 := rfl
        rw [e0]
        simp [Fin.ext_iff, Fin.val_succ]
      rw [h1, mul_zero, zero_mul]
    rw [hrest', add_zero]
    have hC : ((CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ).submatrix
        Fin.succ (Fin.succAbove (0 : Fin (m + 1))) = CM m (fun i => u (i + 2)) := by
      ext i j
      simp only [Fin.zero_succAbove, submatrix_apply, CM]
      have e1 : (Fin.succAbove (1 : Fin (m + 2))) i.succ = i.succ.succ := by
        rw [Fin.succAbove_of_le_castSucc]
        simp [Fin.le_iff_val_le_val]
      rw [e1]
      simp [Fin.ext_iff, Fin.val_succ]
    have h00 :
        (CM (m + 2) u).submatrix (Fin.succAbove (1 : Fin (m + 2))) Fin.succ 0 0 = -C (u 0) := by
      simp only [submatrix_apply, CM]
      have e0 : (Fin.succAbove (1 : Fin (m + 2))) 0 = 0 := rfl
      rw [e0]
      simp
    rw [hC, h00]
    simp
  have h00 : CM (m + 2) u 0 0 = X := by simp [CM]
  have h10 : CM (m + 2) u (Fin.succ 0) 0 = C (u 0) := by simp [CM]
  rw [hA, hB, h00, h10]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, zero_add, pow_one, C_pow]
  ring

/-- The matching polynomial has degree at most half the number of vertices. -/
lemma natDegree_Dv_le (s : ℕ → ℤ) : ∀ j, (Dv s j).natDegree ≤ j / 2
  | 0 => by simp
  | 1 => by simp
  | j + 2 => by
      rw [Dv_succ_succ]
      have h1 := natDegree_Dv_le s (j + 1)
      have h0 := natDegree_Dv_le s j
      apply (natDegree_add_le _ _).trans
      apply max_le
      · exact h1.trans (by omega)
      · apply (natDegree_mul_le).trans
        have : (C (s j : ℤ) * X : ℤ[X]).natDegree ≤ 1 := by
          apply (natDegree_C_mul_le _ _).trans; simp
        omega

/-- The expanded matching polynomial `x ↦ x²`, mapped to `ℂ`. -/
noncomputable def E (s : ℕ → ℤ) (j : ℕ) : ℂ[X] := expand ℂ 2 ((Dv s j).map (Int.castRingHom ℂ))

lemma natDegree_E_le (s : ℕ → ℤ) (j : ℕ) : (E s j).natDegree ≤ j := by
  unfold E
  rw [natDegree_expand]
  have h1 := natDegree_map_le (f := Int.castRingHom ℂ) (p := Dv s j)
  have h2 := natDegree_Dv_le s j
  have : (Polynomial.map (Int.castRingHom ℂ) (Dv s j)).natDegree * 2 ≤ j / 2 * 2 := by
    exact Nat.mul_le_mul_right 2 (h1.trans h2)
  omega

/-- The characteristic polynomial of `T m u` is the reflection of `E s m`, where `s = u²`. -/
lemma det_CM_eq : ∀ (m : ℕ) (s : ℕ → ℤ) (u : ℕ → ℂ), (∀ i, (s i : ℂ) = u i ^ 2) →
    (CM m u).det = reflect m (E s m)
  | 0, s, u, _ => by simp [E]
  | 1, s, u, _ => by
      rw [det_CM_one]
      simp [E]
  | m + 2, s, u, hsu => by
      rw [det_CM_succ_succ,
        det_CM_eq (m + 1) (fun i => s (i + 1)) (fun i => u (i + 1)) (fun i => hsu _),
        det_CM_eq m (fun i => s (i + 2)) (fun i => u (i + 2)) (fun i => hsu _)]
      have hE : E s (m + 2) = E (fun i => s (i + 1)) (m + 1)
          + C (u 0 ^ 2) * X ^ 2 * E (fun i => s (i + 2)) m := by
        simp only [E]
        rw [Dv_succ_succ_left, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          Polynomial.map_C, Polynomial.map_X, map_add, map_mul, map_mul, expand_C, expand_X,
          ← hsu 0]
        simp
      rw [hE, reflect_add]
      -- the first term gains a factor X, the second loses X²
      have h1 : reflect (m + 2) (E (fun i => s (i + 1)) (m + 1))
          = X * reflect (m + 1) (E (fun i => s (i + 1)) (m + 1)) := by
        have := reflect_mul (1 : ℂ[X]) (E (fun i => s (i + 1)) (m + 1)) (F := 1) (G := m + 1)
          (by simp) (natDegree_E_le _ _)
        rw [one_mul, show 1 + (m + 1) = m + 2 by omega] at this
        rw [this, show (1 : ℂ[X]) = C 1 by simp, reflect_C]
        simp
      have h2 : reflect (m + 2) (C (u 0 ^ 2) * X ^ 2 * E (fun i => s (i + 2)) m)
          = C (u 0 ^ 2) * reflect m (E (fun i => s (i + 2)) m) := by
        have := reflect_mul (C (u 0 ^ 2) * X ^ 2) (E (fun i => s (i + 2)) m) (F := 2) (G := m)
          (by apply (natDegree_C_mul_le _ _).trans; simp) (natDegree_E_le _ _)
        rw [show 2 + m = m + 2 by omega] at this
        rw [this, reflect_C_mul_X_pow, revAt_le (le_refl 2), Nat.sub_self, pow_zero, mul_one]
      rw [h1, h2]

/-- A complex square matrix is nilpotent iff its characteristic polynomial is `X ^ size`. -/
lemma isNilpotent_iff_charpoly_matrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    IsNilpotent A ↔ A.charpoly = X ^ m := by
  have h := LinearMap.isNilpotent_iff_charpoly (Matrix.toLin' A)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Matrix.charpoly_toLin'] at h
  rw [← h]
  exact (IsNilpotent.map_iff (f := Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin m))
    (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin m)).injective).symm

/-- `reflect m (E s m) = X ^ m` iff `Dv s m = 1`. -/
lemma reflect_E_eq_iff (s : ℕ → ℤ) (m : ℕ) : reflect m (E s m) = X ^ m ↔ Dv s m = 1 := by
  rw [← reflect_one (R := ℂ) m]
  constructor
  · intro h
    have hE : E s m = 1 := by
      simpa only [reflect_reflect] using congrArg (reflect m) h
    unfold E at hE
    have h1 : Polynomial.map (Int.castRingHom ℂ) (Dv s m) = 1 := by
      apply expand_injective (R := ℂ) (n := 2) (by norm_num)
      rw [hE, map_one]
    have hinj : Function.Injective (Polynomial.map (Int.castRingHom ℂ)) :=
      Polynomial.map_injective _ (RingHom.injective_int _)
    exact hinj (by rw [h1, Polynomial.map_one])
  · intro h
    simp [E, h]

/-- **Corless's conjecture, matrix form.** For `u` with entries in `{1, i}`, the matrix `T m u`
is nilpotent iff the signs `u²` satisfy `Dv = 1`, i.e. (by `corless`) iff `m = 2^(k+1) - 1` and
the signs form one of Corless's sequences. -/
theorem T_nilpotent_iff {u : ℕ → ℂ} (hu : ∀ i, u i = 1 ∨ u i = Complex.I) {m : ℕ} (hm : 1 ≤ m) :
    IsNilpotent (T m u) ↔
      ∃ k, m = 2 ^ (k + 1) - 1 ∧ Fam k (fun i => if u i = 1 then 1 else -1) := by
  set s : ℕ → ℤ := fun i => if u i = 1 then 1 else -1 with hs
  have hsu : ∀ i, (s i : ℂ) = u i ^ 2 := by
    intro i
    rcases hu i with h | h
    · simp [hs, h]
    · have hI : Complex.I ≠ 1 := fun h' => by
        have := congrArg Complex.re h'
        simp at this
      simp [hs, h, hI]
  have hsign : IsSign s := by
    intro i
    by_cases h : u i = 1 <;> simp [hs, h]
  rw [isNilpotent_iff_charpoly_matrix, Matrix.charpoly, charmatrix_T, det_CM_eq m s u hsu,
    reflect_E_eq_iff, corless hsign hm]

end Corless
