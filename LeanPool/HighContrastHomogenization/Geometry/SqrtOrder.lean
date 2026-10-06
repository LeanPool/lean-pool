/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization: Geometry.SqrtOrder

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Operator monotonicity of the square root

The joint monotonicity of the matrix geometric mean rests on the fact that
`H ↦ H^{1/2}` is monotone for the Loewner order.  The reference text proves that
from the integral representation of the matrix square root; the argument here is
the equivalent norm argument, which needs no vector-valued integral.

Write `S`, `T` for the square roots of `A ≤ B`, with `B` positive definite, and
put `W := T^{-1/2} S T^{-1/2}`.  Conjugating `A ≤ B` by `T^{-1}` shows that
`(S T^{-1})^t (S T^{-1}) ≤ I`, so `‖S T^{-1}‖ ≤ 1`.  The powers of `W` telescope
through `S T^{-1}`, so `‖W^m‖` is bounded uniformly in `m`, while `‖W^{2^k}‖`
equals `‖W‖^{2^k}` because `W` is symmetric.  Hence `‖W‖ ≤ 1`, that is `W ≤ I`,
and conjugating back gives `S ≤ T`.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The C⋆ identity in the form used below: a symmetric matrix has
`‖X * X‖ = ‖X‖ ^ 2`. -/
private theorem norm_mul_self_of_symm {X : Matrix n n ℝ} (hX : Xᴴ = X) :
    ‖X * X‖ = ‖X‖ ^ 2 := by
  have h := CStarRing.norm_star_mul_self (x := X)
  rw [Matrix.star_eq_conjTranspose, hX] at h
  rw [h, sq]

/-- A positive semidefinite matrix bounded by the identity has norm at most
one. -/
private theorem norm_le_one_of_le_one {X : Matrix n n ℝ} (hX : X.PosSemidef)
    (h : X ≤ 1) : ‖X‖ ≤ 1 := by
  refine norm_le_of_le_smul_one hX zero_le_one ?_
  rwa [one_smul]

/-- Powers of a Hermitian matrix are Hermitian. -/
private theorem isHermitian_pow {X : Matrix n n ℝ} (hX : Xᴴ = X) (m : ℕ) :
    (X ^ m)ᴴ = X ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.conjTranspose_mul, hX, ih, ← pow_succ', pow_succ]

/-- **Operator monotonicity of the square root.**  This is the substantive step
in the joint monotonicity of the matrix geometric mean. -/
theorem matSqrt_le_matSqrt {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosDef)
    (h : A ≤ B) : matSqrt A ≤ matSqrt B := by
  set S : Matrix n n ℝ := matSqrt A with hSdef
  set T : Matrix n n ℝ := matSqrt B with hTdef
  have hSpsd : S.PosSemidef := (matSqrt_spec hA).1
  have hSS : S * S = A := (matSqrt_spec hA).2
  have hSsymm : Sᴴ = S := hSpsd.isHermitian
  have hT : T.PosDef := posDef_matSqrt hB
  have hTT : T * T = B := (matSqrt_spec hB.posSemidef).2
  have hTsymm : Tᴴ = T := hT.isHermitian
  have hTdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hB)
  have hTinvsymm : (T⁻¹)ᴴ = T⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hTsymm]
  -- `T⁻¹ B T⁻¹ = I`.
  have hTBT : T⁻¹ * B * T⁻¹ = 1 := by
    calc T⁻¹ * B * T⁻¹ = T⁻¹ * (T * T) * T⁻¹ := by rw [hTT]
      _ = (T⁻¹ * T) * (T * T⁻¹) := by noncomm_ring
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hTdet, Matrix.mul_nonsing_inv _ hTdet, Matrix.one_mul]
  -- Step 1: `‖S T⁻¹‖ ≤ 1`.
  set N : Matrix n n ℝ := S * T⁻¹ with hNdef
  have hNN : Nᴴ * N = T⁻¹ * A * T⁻¹ := by
    rw [hNdef, Matrix.conjTranspose_mul, hTinvsymm, hSsymm]
    calc T⁻¹ * S * (S * T⁻¹) = T⁻¹ * (S * S) * T⁻¹ := by noncomm_ring
      _ = T⁻¹ * A * T⁻¹ := by rw [hSS]
  have hNpsd : (Nᴴ * N).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self N
  have hNle : Nᴴ * N ≤ 1 := by
    have hc := conj_le_conj' hTinvsymm h
    rw [hTBT] at hc
    rwa [hNN]
  have hNnorm : ‖N‖ ≤ 1 := by
    have h1 : ‖Nᴴ * N‖ ≤ 1 := norm_le_one_of_le_one hNpsd hNle
    rw [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self (x := N)] at h1
    nlinarith only [h1, norm_nonneg N]
  -- Step 2: the powers of `W` telescope through `N`.
  set Q : Matrix n n ℝ := matSqrt T⁻¹ with hQdef
  have hQ : Q.PosDef := posDef_matSqrt hT.inv
  have hQsymm : Qᴴ = Q := hQ.isHermitian
  have hQQ : Q * Q = T⁻¹ := (matSqrt_spec hT.inv.posSemidef).2
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt hT.inv)
  set W : Matrix n n ℝ := Q * S * Q with hWdef
  have hWpsd : W.PosSemidef := by
    have hc := hSpsd.conjTranspose_mul_mul_same (B := Q)
    rwa [hQsymm] at hc
  have hWsymm : Wᴴ = W := hWpsd.isHermitian
  have hfact : ∀ m : ℕ, W ^ (m + 1) = Q * N ^ m * S * Q := by
    intro m
    induction m with
    | zero => simp [hWdef]
    | succ k ih =>
        have hstep : W ^ (k + 2) = (Q * N ^ k * S * Q) * W := by
          rw [pow_succ, ih]
        rw [hstep, hWdef]
        calc Q * N ^ k * S * Q * (Q * S * Q)
            = Q * N ^ k * S * (Q * Q) * S * Q := by noncomm_ring
          _ = Q * N ^ k * (S * T⁻¹) * S * Q := by rw [hQQ]; noncomm_ring
          _ = Q * N ^ (k + 1) * S * Q := by rw [← hNdef, pow_succ]; noncomm_ring
  set C₀ : ℝ := ‖Q‖ * ‖S‖ * ‖Q‖ with hC₀def
  have hC₀ : 0 ≤ C₀ := by positivity
  have hbound : ∀ m : ℕ, 1 ≤ m → ‖W ^ m‖ ≤ C₀ := by
    intro m hm
    match m, hm with
    | 1, _ =>
        rw [pow_one, hWdef]
        calc ‖Q * S * Q‖ ≤ ‖Q * S‖ * ‖Q‖ := norm_mul_le _ _
          _ ≤ (‖Q‖ * ‖S‖) * ‖Q‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Q)
    | (k + 2), _ =>
        have hNk : ‖N ^ (k + 1)‖ ≤ 1 := by
          have h1 : ‖N ^ (k + 1)‖ ≤ ‖N‖ ^ (k + 1) := norm_pow_le' N k.succ_pos
          have h2 : ‖N‖ ^ (k + 1) ≤ 1 ^ (k + 1) :=
            pow_le_pow_left₀ (norm_nonneg N) hNnorm (k + 1)
          rw [one_pow] at h2
          exact h1.trans h2
        rw [hfact (k + 1)]
        calc ‖Q * N ^ (k + 1) * S * Q‖
            ≤ ‖Q * N ^ (k + 1) * S‖ * ‖Q‖ := norm_mul_le _ _
          _ ≤ (‖Q * N ^ (k + 1)‖ * ‖S‖) * ‖Q‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Q)
          _ ≤ ((‖Q‖ * ‖N ^ (k + 1)‖) * ‖S‖) * ‖Q‖ := by
              have := norm_mul_le Q (N ^ (k + 1))
              have h3 : ‖Q * N ^ (k + 1)‖ * ‖S‖ ≤ (‖Q‖ * ‖N ^ (k + 1)‖) * ‖S‖ :=
                mul_le_mul_of_nonneg_right this (norm_nonneg S)
              exact mul_le_mul_of_nonneg_right h3 (norm_nonneg Q)
          _ ≤ ((‖Q‖ * 1) * ‖S‖) * ‖Q‖ := by
              have h4 : ‖Q‖ * ‖N ^ (k + 1)‖ ≤ ‖Q‖ * 1 :=
                mul_le_mul_of_nonneg_left hNk (norm_nonneg Q)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h4 (norm_nonneg S)) (norm_nonneg Q)
          _ = C₀ := by rw [hC₀def]; ring
  -- Step 3: `‖W^{2^k}‖ = ‖W‖^{2^k}`.
  have hpow : ∀ k : ℕ, ‖W ^ 2 ^ k‖ = ‖W‖ ^ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hsplit : (2 : ℕ) ^ (j + 1) = 2 ^ j + 2 ^ j := by ring
        rw [hsplit, pow_add, norm_mul_self_of_symm (isHermitian_pow hWsymm (2 ^ j)), ih,
          ← pow_mul, mul_two]
  -- Step 4: `‖W‖ ≤ 1`.
  have hWnorm : ‖W‖ ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (R := ℝ) C₀ hcon
    have hmono : ‖W‖ ^ m ≤ ‖W‖ ^ 2 ^ m :=
      pow_le_pow_right₀ hcon.le (Nat.le_of_lt (Nat.lt_two_pow_self))
    have hle := hbound (2 ^ m) (Nat.one_le_two_pow)
    rw [hpow m] at hle
    linarith only [hm, hmono, hle]
  -- Step 5: conjugate back.
  have hWle : W ≤ 1 := by
    have := le_smul_one_of_norm_le hWpsd hWnorm
    rwa [one_smul] at this
  have hQinvsymm : (Q⁻¹)ᴴ = Q⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hQsymm]
  have hcong := conj_le_conj' hQinvsymm hWle
  have hleft : Q⁻¹ * W * Q⁻¹ = S := by
    rw [hWdef]
    calc Q⁻¹ * (Q * S * Q) * Q⁻¹ = (Q⁻¹ * Q) * S * (Q * Q⁻¹) := by noncomm_ring
      _ = S := by
          rw [Matrix.nonsing_inv_mul _ hQdet, Matrix.mul_nonsing_inv _ hQdet,
            Matrix.one_mul, Matrix.mul_one]
  have hright : Q⁻¹ * 1 * Q⁻¹ = T := by
    rw [Matrix.mul_one, ← Matrix.mul_inv_rev, hQQ,
      Matrix.nonsing_inv_nonsing_inv _ hTdet]
  rwa [hleft, hright] at hcong

end

end HighContrast
end HCPolySupport
