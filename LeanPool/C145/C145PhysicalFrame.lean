/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Physical frames

`Fin (n + 1)` indexes both vertices and modes. Mode zero is retained in every
contraction, even when `n = 0`. These are finite counting-metric identities.
Nonzero modal overlaps/diagonal weights suffice for the algebra; positivity,
spectral calibration, graph realization, and response recovery are later work.
-/

@[expose] public section

namespace C145PhysicalFrame

noncomputable section

open scoped BigOperators

/-- Unit-norm pairwise orthogonal columns of the square coordinate frame. -/
def ColumnOrthonormal {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) : Prop :=
  ∀ i j, (∑ v, Q v i * Q v j) = if i = j then 1 else 0

/-- The source's cubic coordinate multiplication tensor. -/
def C {n : ℕ} (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j k : Fin (n + 1)) : ℝ :=
  ∑ v, Q v i * Q v j * Q v k

/-- The source's modal tensor with all three port-overlap factors. -/
def T {n : ℕ} (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (i j k : Fin (n + 1)) : ℝ :=
  a i * a j * a k * C Q i j k

/-- Pairing of covectors, summing over every output mode including ground. -/
def Pair {n : ℕ} (a r s : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, r k * s k / a k ^ 2

/-- The source's weighted associativity residual; the ground summand remains. -/
def Assoc {n : ℕ} (a : Fin (n + 1) → ℝ)
    (S : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j k l : Fin (n + 1)) : ℝ :=
  ∑ r, (S i k r * S j l r - S i l r * S j k r) / a r ^ 2

/-- The frame rows have Kronecker-delta inner products. -/
def RowComplete {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) : Prop :=
  ∀ v u, (∑ r, Q v r * Q u r) = if v = u then 1 else 0

/-- A left inverse supplied by the explicit weighted Gram sums is also a right
inverse because the frame is square. No row-completeness premise is supplied. -/
theorem weighted_row_complete {n : ℕ}
    (F : Fin (n + 1) → Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ)
    (hw : ∀ i, w i ≠ 0)
    (hgram : ∀ i j, (∑ v, F v i * F v j) =
      w i * (if i = j then 1 else 0))
    (v u : Fin (n + 1)) :
    (∑ r, F v r * F u r / w r) = if v = u then 1 else 0 := by
  classical
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of F
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of (fun i x => F x i / w i)
  have hBF : B * A = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, A, B, Matrix.of_apply]
    calc
      (∑ x, F x i / w i * F x j) = (∑ x, F x i * F x j) / w i := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = if i = j then 1 else 0 := by
        rw [hgram i j]
        by_cases hij : i = j <;> simp [hij, hw j]
  have hFB : A * B = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin (n + 1)))).mp hBF
  have hentry := congrFun (congrFun hFB v) u
  simpa only [Matrix.mul_apply, Matrix.one_apply, A, B, Matrix.of_apply,
    mul_div_assoc] using hentry

/-- Expanding two actual cubic tensors and using the derived weighted row sum
collapses their contraction to a quartic vertex sum. -/
theorem weighted_cubic_contraction {n : ℕ}
    (F : Fin (n + 1) → Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ)
    (hw : ∀ i, w i ≠ 0)
    (hgram : ∀ i j, (∑ v, F v i * F v j) =
      w i * (if i = j then 1 else 0))
    (i j k l : Fin (n + 1)) :
    (∑ r, C F i k r * C F j l r / w r) =
      ∑ v, F v i * F v j * F v k * F v l := by
  classical
  calc
    (∑ r, C F i k r * C F j l r / w r) =
        ∑ r, ∑ v, ∑ u,
          (F v i * F v k * F v r) * (F u j * F u l * F u r) / w r := by
      simp only [C, Finset.sum_mul_sum, Finset.sum_div]
    _ = ∑ v, ∑ u, ∑ r,
          (F v i * F v k * F v r) * (F u j * F u l * F u r) / w r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
    _ = ∑ v, ∑ u, (F v i * F v k * F u j * F u l) *
          (∑ r, F v r * F u r / w r) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ v, ∑ u, (F v i * F v k * F u j * F u l) *
          (if v = u then 1 else 0) := by
      simp_rw [weighted_row_complete F w hw hgram]
    _ = ∑ v, F v i * F v j * F v k * F v l := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      ring

theorem columnOrthonormal_rowComplete {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ : ColumnOrthonormal Q) : RowComplete Q := by
  intro v u
  simpa only [div_one] using
    weighted_row_complete Q (fun _ => 1) (fun _ => one_ne_zero)
      (fun i j => by simpa only [one_mul] using hQ i j) v u

theorem cubic_contraction {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ : ColumnOrthonormal Q) (i j k l : Fin (n + 1)) :
    (∑ r, C Q i k r * C Q j l r) =
      ∑ v, Q v i * Q v j * Q v k * Q v l := by
  simpa only [div_one] using
    weighted_cubic_contraction Q (fun _ => 1) (fun _ => one_ne_zero)
      (fun x y => by simpa only [one_mul] using hQ x y) i j k l

/-- The constant ground column is normalized by column orthonormality itself. -/
theorem ground_normalization {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : ColumnOrthonormal Q) (hground : ∀ v, Q v 0 = c) :
    (n + 1 : ℝ) * c ^ 2 = 1 := by
  simpa only [hground, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_two] using hQ 0 0

theorem ground_ne_zero {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : ColumnOrthonormal Q) (hground : ∀ v, Q v 0 = c) : c ≠ 0 := by
  intro hc
  have h := ground_normalization Q c hQ hground
  exact (zero_ne_one : (0 : ℝ) ≠ 1) (by simp [hc] at h)

theorem ground_slice {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : ColumnOrthonormal Q) (hground : ∀ v, Q v 0 = c)
    (j k : Fin (n + 1)) :
    T Q a 0 j k = a 0 * c * a j ^ 2 * (if j = k then 1 else 0) := by
  have hC : C Q 0 j k = c * (if j = k then 1 else 0) := by
    calc
      C Q 0 j k = c * ∑ v, Q v j * Q v k := by
        simp only [C, hground, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = c * (if j = k then 1 else 0) := by rw [hQ j k]
  rw [T, hC]
  by_cases hjk : j = k
  · subst k
    simp only
    ring
  · simp [hjk]

theorem modal_associativity {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (hQ : ColumnOrthonormal Q)
    (ha : ∀ i, a i ≠ 0) (i j k l : Fin (n + 1)) :
    Assoc a (T Q a) i j k l = 0 := by
  have hcancel (r : Fin (n + 1)) :
      (T Q a i k r * T Q a j l r - T Q a i l r * T Q a j k r) / a r ^ 2 =
        (a i * a j * a k * a l) *
          (C Q i k r * C Q j l r - C Q i l r * C Q j k r) := by
    dsimp only [T]
    field_simp [ha r]
  have hquartic : (∑ v, Q v i * Q v j * Q v k * Q v l) =
      ∑ v, Q v i * Q v j * Q v l * Q v k := by
    apply Finset.sum_congr rfl
    intro v hv
    ring
  simp only [Assoc, hcancel, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [cubic_contraction Q hQ i j k l, cubic_contraction Q hQ i j l k,
    hquartic, sub_self, mul_zero]

/-- Counting-metric trace before using orthogonality to the ground column. -/
theorem modal_counting_trace {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (hQ : ColumnOrthonormal Q)
    (ha : ∀ i, a i ≠ 0) (i : Fin (n + 1)) :
    (∑ j, T Q a i j j / a j ^ 2) = a i * ∑ v, Q v i := by
  have hdiag (v : Fin (n + 1)) : (∑ j, Q v j * Q v j) = 1 := by
    simpa only [ite_true] using columnOrthonormal_rowComplete Q hQ v v
  calc
    (∑ j, T Q a i j j / a j ^ 2) = ∑ j, a i * C Q i j j := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [T]
      field_simp [ha j]
    _ = a i * ∑ v, Q v i * (∑ j, Q v j * Q v j) := by
      simp only [C, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = a i * ∑ v, Q v i := by simp_rw [hdiag]; simp only [mul_one]

theorem nonground_counting_trace {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : ColumnOrthonormal Q) (ha : ∀ i, a i ≠ 0)
    (hground : ∀ v, Q v 0 = c) (i : Fin n) :
    (∑ j, T Q a i.succ j j / a j ^ 2) = 0 := by
  have hc : c ≠ 0 := ground_ne_zero Q c hQ hground
  have horth : (∑ v, Q v i.succ) * c = 0 := by
    calc
      (∑ v, Q v i.succ) * c = ∑ v, Q v i.succ * c := by rw [Finset.sum_mul]
      _ = ∑ v, Q v i.succ * Q v 0 := by simp_rw [hground]
      _ = 0 := by simpa only [Fin.succ_ne_zero, ite_false] using hQ i.succ 0
  have hsum : (∑ v, Q v i.succ) = 0 := (mul_eq_zero.mp horth).resolve_right hc
  rw [modal_counting_trace Q a hQ ha i.succ, hsum, mul_zero]

/-- Exactly the first package in the accepted central plan, with every scientific
premise visible. Ground normalization/nonvanishing are proved above, not inputs. -/
theorem physical_frame_identities
    (n : ℕ) (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ : ColumnOrthonormal Q) (ha : ∀ i, a i ≠ 0)
    (hground : ∀ v, Q v 0 = c) :
    RowComplete Q ∧
      (∀ i j k l, Assoc a (T Q a) i j k l = 0) ∧
      (∀ j k, T Q a 0 j k = a 0 * c * a j ^ 2 * (if j = k then 1 else 0)) ∧
      (∀ i : Fin n, (∑ j, T Q a i.succ j j / a j ^ 2) = 0) := by
  exact ⟨columnOrthonormal_rowComplete Q hQ, modal_associativity Q a hQ ha,
    ground_slice Q a c hQ hground, nonground_counting_trace Q a c hQ ha hground⟩

/-- Rational-frame interface: `C F` is the explicit cubic sum called `TF` in
the plan. No square root, reconstruction, physical realization, or rank input. -/
theorem weighted_frame_identities
    (n : ℕ) (F : Fin (n + 1) → Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ)
    (hw : ∀ i, w i ≠ 0)
    (hgram : ∀ i j, (∑ v, F v i * F v j) =
      w i * (if i = j then 1 else 0)) :
    (∀ v u, (∑ r, F v r * F u r / w r) = if v = u then 1 else 0) ∧
      (∀ i j k l, (∑ r,
        (C F i k r * C F j l r - C F i l r * C F j k r) / w r) = 0) := by
  refine ⟨weighted_row_complete F w hw hgram, ?_⟩
  intro i j k l
  simp only [sub_div, Finset.sum_sub_distrib]
  rw [weighted_cubic_contraction F w hw hgram i j k l,
    weighted_cubic_contraction F w hw hgram i j l k]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro v hv
  ring


end

end C145PhysicalFrame

end
