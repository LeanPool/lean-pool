/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Profiles

/-! The pieces of `psiL` and `phiL` (the proof notes, §8.5).

In the variable `u = 1/x` (for a prime, `u = n/p`), the relaxed range `(1/20, 7/3]` of `x` is
the range
`[3/7, 20)` of `u`, cut at the points `m + α` (`m ∈ ℕ`, `α ∈ {0, 1/5, 1/4, 1/3, 2/5, 1/2, 3/5,
2/3, 3/4, 4/5}`)
into 196 half-open pieces `[ub i, ub (i+1))`. On the piece with `⌊u⌋ = m` and `{u}` in the
`k`-th cell,
`psiL x = cellA k m + cellB k m · x − 25/(4x)` (the ten parametric formulas, proved once for all
`m`).
The outer range `(7/3, 5]` of `x` is `[1/5, 3/7)` in `u`, four pieces on which `phiL` is linear.
The tail `x ≤ 1/20` is handled by the global bound `psiL x ≤ 33/5 + (121/100) x`. -/

@[expose] public section

namespace Zeta32.ArithSum
noncomputable section

/-! ### The cells of `[0,1]` and the ten formulas -/

/-- Breakpoints of the cells of `[0, 1]` (partition by `j/3, j/4, j/5`). -/
def alphaQ : ℕ → ℚ
  | 0 => 0 | 1 => 1/5 | 2 => 1/4 | 3 => 1/3 | 4 => 2/5 | 5 => 1/2 | 6 => 3/5 | 7 => 2/3
  | 8 => 3/4 | 9 => 4/5 | _ => 1

/-- Constant coefficient on cell `k` (with `m = ⌊1/x⌋`). -/
def cellA : ℕ → ℚ → ℚ
  | 0, m => (62*m+49)/4 | 1, m => (62*m+7)/4 | 2, m => (62*m+39)/4 | 3, m => (62*m+63)/4
  | 4, m => (62*m+21)/4 | 5, m => (62*m+53)/4 | 6, m => (62*m+11)/4 | 7, m => (62*m+35)/4
  | 8, m => (62*m+67)/4 | _, m => (62*m+25)/4

/-- Coefficient of `x` on cell `k`. -/
def cellB : ℕ → ℚ → ℚ
  | 0, m => -(m*(37*m+25))/4 | 1, m => -(37*m^2-5*m-6)/4 | 2, m => -(37*m^2+27*m+2)/4
  | 3, m => -(37*m^2+51*m+10)/4 | 4, m => -(37*m^2+21*m-2)/4 | 5, m => -(37*m^2+53*m+14)/4
  | 6, m => -(37*m^2+23*m-4)/4 | 7, m => -(37*m^2+47*m+12)/4 | 8, m => -(37*m^2+79*m+36)/4
  | _, m => -((m+1)*(37*m+12))/4

lemma fract_eq_sub (y : ℝ) (z : ℤ) (h1 : (z : ℝ) ≤ y) (h2 : y < z + 1) :
    Int.fract y = y - z := by
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨h1, h2⟩]

/-- `psiL` in terms of the three fractional parts (definitional unfolding). -/
lemma psiL_eq (x : ℝ) : psiL x =
    6 + x * Int.fract (3/x) * (1 - Int.fract (3/x)) - 3 * (4 * Int.fract (1/x) - Int.fract (5/x)) +
      x / 4 * (16 * Int.fract (1/x) + Int.fract (5/x) - 8 * min (Int.fract (1/x)) (Int.fract
        (5/x)) -
        (4 * Int.fract (1/x) - Int.fract (5/x)) ^ 2) := rfl

/-- The ten parametric formulas: on the cell `k` of the unit interval, shifted by `m`. -/
theorem psiL_cell (k : ℕ) (hk : k < 10) (m : ℕ) {x : ℝ} (hx : 0 < x)
    (h1 : (m : ℝ) + (alphaQ k : ℝ) ≤ 1 / x) (h2 : 1 / x < (m : ℝ) + (alphaQ (k + 1) : ℝ)) :
    psiL x = (cellA k m : ℝ) + (cellB k m : ℝ) * x - 25 / (4 * x) := by
  have hxU : x * (1 / x) = 1 := mul_one_div_cancel hx.ne'
  rw [psiL_eq, ← mul_one_div 5 x, ← mul_one_div 3 x, div_mul_eq_div_mul_one_div (25 : ℝ) 4 x]
  generalize 1 / x = u at h1 h2 hxU ⊢
  -- After subtracting the affine expression, the residual is a multiple of x * u - 1.
  -- Its coefficient uses the shifts in the two scaled fractional parts and the chosen minimum.
  interval_cases k <;> simp only [alphaQ, Nat.reduceAdd] at h1 h2 <;> push_cast at h1 h2
  · -- cell 0: α ∈ [0, 1/5)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 25) / 4) * hxU
  · -- cell 1: α ∈ [1/5, 1/4)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u - 5) / 4) * hxU
  · -- cell 2: α ∈ [1/4, 1/3)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 27) / 4) * hxU
  · -- cell 3: α ∈ [1/3, 2/5)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 51) / 4) * hxU
  · -- cell 4: α ∈ [2/5, 1/2)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 21) / 4) * hxU
  · -- cell 5: α ∈ [1/2, 3/5)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 53) / 4) * hxU
  · -- cell 6: α ∈ [3/5, 2/3)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 3 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 1 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 23) / 4) * hxU
  · -- cell 7: α ∈ [2/3, 3/4)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 3 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 47) / 4) * hxU
  · -- cell 8: α ∈ [3/4, 4/5)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 3 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_left (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 79) / 4) * hxU
  · -- cell 9: α ∈ [4/5, 1)
    rw [fract_eq_sub u (m : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (5 * u) (5 * m + 4 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2]),
      fract_eq_sub (3 * u) (3 * m + 2 : ℤ)
      (by push_cast; linarith only [h1, h2])
      (by push_cast; linarith only [h1, h2])]
    push_cast
    rw [min_eq_right (by linarith only [h1, h2])]
    simp only [cellA, cellB]; push_cast
    linear_combination ((74 * (m : ℝ) - 37 * u + 49) / 4) * hxU

/-! ### The 196 pieces of the relaxed range, indexed flatly -/

/-- Integer part `m` of piece `i` (pieces `0..5` have `m = 0`, cells `4..9`). -/
def pm (i : ℕ) : ℕ := if i < 6 then 0 else (i - 6) / 10 + 1
/-- Cell `k` of piece `i`. -/
def pk (i : ℕ) : ℕ := if i < 6 then i + 4 else (i - 6) % 10
/-- Left endpoint (in `u = 1/x`) of piece `i`; piece `0` starts at `3/7` inside cell `4`. -/
def ub (i : ℕ) : ℚ := if i = 0 then 3/7 else (pm i : ℚ) + alphaQ (pk i)
/-- Coefficients of piece `i`: `psiL x = pa i + pb i · x − 25/(4x)`. -/
def pa (i : ℕ) : ℚ := cellA (pk i) (pm i)
/-- Constant term of the affine arithmetic-profile cell selected by `i`. -/
def pb (i : ℕ) : ℚ := cellB (pk i) (pm i)

lemma pk_lt (i : ℕ) : pk i < 10 := by
  unfold pk; split_ifs <;> omega

lemma pm_pk_succ (i : ℕ) :
    (pk i < 9 ∧ pm (i + 1) = pm i ∧ pk (i + 1) = pk i + 1) ∨
      (pk i = 9 ∧ pm (i + 1) = pm i + 1 ∧ pk (i + 1) = 0) := by
  unfold pm pk
  split_ifs <;> omega

lemma ub_succ (i : ℕ) : ub (i + 1) = (pm i : ℚ) + alphaQ (pk i + 1) := by
  simp only [ub, Nat.add_one_ne_zero, ↓reduceIte]
  rcases pm_pk_succ i with ⟨_, h1, h2⟩ | ⟨h0, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, h0]
    simp only [alphaQ]
    push_cast
    ring

lemma ub_ge (i : ℕ) : (pm i : ℚ) + alphaQ (pk i) ≤ ub i := by
  unfold ub
  split_ifs with h
  · subst h; simp [pm, pk, alphaQ]; norm_num
  · exact le_rfl

lemma alphaQ_lt (k : ℕ) (hk : k < 10) : alphaQ k < alphaQ (k + 1) := by
  -- Check the ten closed comparisons between rational breakpoints.
  have steps : ∀ i : Fin 10, alphaQ i.val < alphaQ (i.val + 1) := by decide +kernel
  exact steps ⟨k, hk⟩

lemma ub_lt_succ (i : ℕ) : ub i < ub (i + 1) := by
  rw [ub_succ]
  have h := alphaQ_lt (pk i) (pk_lt i)
  unfold ub
  split_ifs with h0
  · subst h0; simp only [pm, pk, alphaQ]; norm_num
  · linarith

lemma ub_zero : ub 0 = 3/7 := rfl

lemma ub_196 : ub 196 = 20 := by
  simp only [ub, pm, pk, alphaQ]; norm_num

lemma ub_pos (i : ℕ) : 0 < ub i := by
  induction i with
  | zero => rw [ub_zero]; norm_num
  | succ i ih => exact ih.trans (ub_lt_succ i)

/-- On piece `i` (for every `i`, in particular the 196 pieces of `[3/7, 20)`), `psiL` is given by
the formula of its cell. -/
theorem psiL_piece (i : ℕ) {x : ℝ} (hx : 0 < x) (h1 : (ub i : ℝ) ≤ 1 / x)
    (h2 : 1 / x < (ub (i + 1) : ℝ)) :
    psiL x = (pa i : ℝ) + (pb i : ℝ) * x - 25 / (4 * x) := by
  have hge : ((pm i : ℚ) + alphaQ (pk i) : ℚ) ≤ ub i := ub_ge i
  have hge' : ((pm i : ℝ) + (alphaQ (pk i) : ℝ)) ≤ (ub i : ℝ) := by exact_mod_cast hge
  have hs : ((ub (i + 1) : ℚ) : ℝ) = (pm i : ℝ) + (alphaQ (pk i + 1) : ℝ) := by
    rw [ub_succ]; push_cast; ring
  rw [hs] at h2
  unfold pa pb
  exact psiL_cell (pk i) (pk_lt i) (pm i) hx (hge'.trans h1) h2

/-! ### The four pieces of the outer range (`7/3 < x ≤ 5`, i.e. `1/5 ≤ u < 3/7`) -/

/-- Rational breakpoints for the reciprocal outer-prime profile. -/
def vb : ℕ → ℚ
  | 0 => 1/5 | 1 => 1/4 | 2 => 1/3 | 3 => 2/5 | _ => 3/7
/-- Constant terms of the affine pieces of the reciprocal outer-prime profile. -/
def vc : ℕ → ℚ
  | 0 => 2 | 1 => 18 | 2 => 24 | _ => 6
/-- Slopes of the affine pieces of the reciprocal outer-prime profile. -/
def vd : ℕ → ℚ
  | 0 => -1 | 1 => -5 | 2 => -7 | _ => -1

lemma vb_lt_succ (i : ℕ) (hi : i < 4) : vb i < vb (i + 1) := by
  -- Check the four closed comparisons between rational breakpoints.
  have steps : ∀ j : Fin 4, vb j.val < vb (j.val + 1) := by decide +kernel
  exact steps ⟨i, hi⟩

theorem phiL_piece (i : ℕ) (hi : i < 4) {x : ℝ} (hx : 0 < x) (h1 : (vb i : ℝ) ≤ 1 / x)
    (h2 : 1 / x < (vb (i + 1) : ℝ)) :
    phiL x = (vc i : ℝ) + (vd i : ℝ) * x := by
  have reciprocal_le {c : ℝ} (hc : 0 < c) : c ≤ 1 / x ↔ x ≤ 1 / c := by
    rw [le_div_iff₀ hx, le_div_iff₀ hc, mul_comm]
  have lt_reciprocal {c : ℝ} (hc : 0 < c) : 1 / x < c ↔ 1 / c < x := by
    rw [div_lt_iff₀ hx, div_lt_iff₀ hc, mul_comm]
  unfold phiL
  interval_cases i <;> simp only [vb, vc, vd, Nat.reduceAdd] at h1 h2 ⊢ <;> push_cast at h1 h2 ⊢
  · have hx4 : 4 < x := by simpa using (lt_reciprocal (by norm_num)).mp h2
    have hx3 : 3 < x := lt_trans (by norm_num) hx4
    have hx5 : 5 / 2 < x := lt_trans (by norm_num) hx3
    rw [ite_eq_right hx5.not_ge, ite_eq_right hx3.not_ge, ite_eq_right hx4.not_ge]
    ring
  · have hx3 : 3 < x := by simpa using (lt_reciprocal (by norm_num)).mp h2
    have hx4 : x ≤ 4 := by simpa using (reciprocal_le (by norm_num)).mp h1
    have hx5 : 5 / 2 < x := lt_trans (by norm_num) hx3
    rw [ite_eq_right hx5.not_ge, ite_eq_right hx3.not_ge, ite_eq_left hx4]
    ring
  · have hx5 : 5 / 2 < x := by
      have h := (lt_reciprocal (by norm_num)).mp h2
      linarith only [h]
    have hx3 : x ≤ 3 := by simpa using (reciprocal_le (by norm_num)).mp h1
    rw [ite_eq_right hx5.not_ge, ite_eq_left hx3]
    ring
  · have hx5 : x ≤ 5 / 2 := by
      have h := (reciprocal_le (by norm_num)).mp h1
      linarith only [h]
    rw [ite_eq_left hx5]
    ring

/-! ### The tail bound -/

-- The real maximum is between two consecutive integers, where the product is at most six.
private lemma int_product_le_six (j : ℤ) : (j : ℝ) * (5 - j) ≤ 6 := by
  have hnonneg : 0 ≤ ((j : ℝ) - 2) * ((j : ℝ) - 3) := by
    rcases le_or_gt j 2 with hj | hj
    · have h2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h2)
        (sub_nonpos.mpr (h2.trans (by norm_num)))
    · have h3 : (3 : ℝ) ≤ j := by exact_mod_cast (show (3 : ℤ) ≤ j by omega)
      exact mul_nonneg (sub_nonneg.mpr ((by norm_num : (2 : ℝ) ≤ 3).trans h3))
        (sub_nonneg.mpr h3)
  linarith only [hnonneg]

lemma quad_bound (a b : ℝ) (j : ℤ) (hj : 5 * a - b = j) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    16 * a + b - 8 * min a b - (4 * a - b) ^ 2 ≤ 96 / 25 ∧ -3 * (4 * a - b) ≤ 3 / 5 := by
  have hj0 : (-1 : ℝ) < j := by rw [← hj]; linarith only [ha0, hb1]
  have hj5 : (j : ℝ) < 5 := by rw [← hj]; linarith only [ha1, hb0]
  have hj0' : (-1 : ℤ) < j := by exact_mod_cast hj0
  have hj5' : j < (5 : ℤ) := by exact_mod_cast hj5
  have hj_nonneg : (0 : ℝ) ≤ j := by exact_mod_cast (show (0 : ℤ) ≤ j by omega)
  have hj_le : (j : ℝ) ≤ 4 := by exact_mod_cast (show j ≤ (4 : ℤ) by omega)
  have hb : b = 5 * a - j := by linarith only [hj]
  have hlo : (j : ℝ) / 5 ≤ a := by linarith only [hb, hb0]
  have hhi : a ≤ ((j : ℝ) + 1) / 5 := by linarith only [hb, hb1]
  constructor
  · rcases le_total a b with hab | hab
    · -- When the minimum is a, the quadratic is increasing up to the upper endpoint.
      rw [min_eq_left hab, hb]
      have slope : 0 ≤ 13 + 2 * (j : ℝ) - (a + ((j : ℝ) + 1) / 5) := by
        linarith only [ha1, hj_le, hj_nonneg]
      have increase := mul_nonneg (sub_nonneg.mpr hhi) slope
      have atEndpoint := int_product_le_six (j + 1)
      push_cast at atEndpoint
      linarith only [increase, atEndpoint]
    · -- When the minimum is b, the lower endpoint gives the upper bound.
      rw [min_eq_right hab, hb]
      have slope : 0 ≤ 19 - 2 * (j : ℝ) + a + (j : ℝ) / 5 := by
        linarith only [ha0, hj_le, hj_nonneg]
      have decrease := mul_nonneg (sub_nonneg.mpr hlo) slope
      linarith only [decrease, int_product_le_six j]
  · linarith only [hb, hhi, hj_nonneg]

/-- `psiL x ≤ 33/5 + (121/100) x` for every `x > 0` (used for `x ≤ 1/20`). -/
theorem psiL_le_tail {x : ℝ} (hx : 0 < x) : psiL x ≤ 33 / 5 + 121 / 100 * x := by
  rw [psiL_eq]
  set a := Int.fract (1 / x) with ha
  set b := Int.fract (5 / x) with hb
  set g := Int.fract (3 / x) with hg
  have hj : 5 * a - b = ((⌊5 / x⌋ - 5 * ⌊1 / x⌋ : ℤ) : ℝ) := by
    rw [ha, hb, Int.fract, Int.fract]
    push_cast
    have : 5 / x = 5 * (1 / x) := by ring
    rw [this]; ring
  obtain ⟨h1, h2⟩ := quad_bound a b _ hj (Int.fract_nonneg _) (Int.fract_lt_one _)
    (Int.fract_nonneg _) (Int.fract_lt_one _)
  have hg1 : g * (1 - g) ≤ 1 / 4 := by nlinarith [sq_nonneg (g - 1 / 2)]
  have hsum : g * (1 - g) + (16 * a + b - 8 * min a b - (4 * a - b) ^ 2) / 4 ≤ 121 / 100 := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum hx.le
  nlinarith [this]

end
end Zeta32.ArithSum

end
