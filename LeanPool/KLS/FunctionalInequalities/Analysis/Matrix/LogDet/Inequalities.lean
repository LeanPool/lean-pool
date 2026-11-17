/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Inequalities for the log-determinant

Two matrix facts used on the weak moment-map route to Letwin's quadratic-form bound
(arXiv:2607.24164v1, Theorem 1.2; BKL arXiv:2610.05474v1, Lemma 4.2):

- `forall_posDef_add_log_det_le_trace_iff`: `log det` as an infimum of linear functions,
  `(∀ J ≻ 0, b + log det J + n ≤ tr(J A)) ↔ (A ≻ 0 ∧ e^b ≤ det A)` for positive semidefinite `A`
  (the distributional form of the Monge–Ampère equation);
- `log_det_add_frobenius_sq_le`: quantitative concavity, for positive definite `A, B ≤ K·Id`,
  `log det B + ‖B − A‖²_F/(2K²) ≤ log det A + tr(A⁻¹(B − A))` (the difference-quotient estimate of
  the
  Hessian of the moment map).

-/

@[expose] public section

section

open Matrix

namespace FunctionalInequalities.Analysis

section LogDetInf

private lemma log_det_add_card_le_trace {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    Real.log M.det + n ≤ M.trace := by
  rw [hM.isHermitian.det_eq_prod_eigenvalues,
    hM.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hM.eigenvalues_pos i))]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hM.eigenvalues_pos i))
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, le_sub_iff_add_le] using h

private lemma exists_posDef_square {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ, B.PosDef ∧ B * B = A := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
    hA.isHermitian.eigenvectorUnitary
  let B := e (diagonal (fun i => Real.sqrt (hA.isHermitian.eigenvalues i)))
  have hp : B.PosDef := by
    dsimp only [B, e]
    rw [Unitary.conjStarAlgAut_apply]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
      (Matrix.posDef_diagonal_iff.mpr
        (fun i => Real.sqrt_pos.mpr (hA.eigenvalues_pos i)))
  refine ⟨B, hp, ?_⟩
  change e _ * e _ = A
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  simp only [Real.mul_self_sqrt (le_of_lt (hA.eigenvalues_pos _))]
  simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    hA.isHermitian.spectral_theorem.symm

private lemma posDef_of_forall_log_det_le_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (b : ℝ)
    (H : ∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) :
    A.PosDef := by
  let e := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) hA.isHermitian.eigenvectorUnitary
  have hs : A = e (diagonal hA.isHermitian.eigenvalues) := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hA.isHermitian.spectral_theorem
  have hd (d : Fin n → ℝ) (hp : ∀ i, 0 < d i) :
    b + Real.log (∏ i, d i) + n ≤ ∑ i, d i * hA.isHermitian.eigenvalues i := by
    have hj : (e (diagonal d)).PosDef := by
      dsimp only [e]
      rw [Unitary.conjStarAlgAut_apply]
      exact
        (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr
          (Matrix.posDef_diagonal_iff.mpr hp)
    have ht : (e (diagonal d) * A).trace = ∑ i, d i * hA.isHermitian.eigenvalues i := by
      conv_lhs => rw [hs]
      rw [← map_mul, Matrix.trace_map, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simpa only [Matrix.det_map, Matrix.det_diagonal, ht] using H _ hj
  apply hA.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  by_contra hi
  have hz : hA.isHermitian.eigenvalues i = 0 :=
    le_antisymm (le_of_not_gt hi) (hA.eigenvalues_nonneg i)
  let t := Real.exp ((∑ j, hA.isHermitian.eigenvalues j) - b + 1)
  have hp (j : Fin n) : 0 < (if i = j then t else 1) := by
    split_ifs
    · exact Real.exp_pos _
    · norm_num
  have h := hd (fun j => if i = j then t else 1) hp
  have he (j : Fin n) :
    (if i = j then t else 1) * hA.isHermitian.eigenvalues j = hA.isHermitian.eigenvalues j := by
    by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, one_mul]
    subst j
    simp only [hz, mul_zero]
  simp only [he, Finset.prod_ite_eq, Finset.mem_univ, ite_true, t, Real.log_exp] at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **`log det` as an infimum of linear functions** (used for the distributional Monge–Ampère trace
inequality): for a positive semidefinite `A` and real `b`,
`(∀ J ≻ 0, b + log det J + n ≤ tr(J A)) ↔ (A ≻ 0 ∧ e^b ≤ det A)`. -/
theorem forall_posDef_add_log_det_le_trace_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (b : ℝ) :
    (∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) ↔
      (A.PosDef ∧ Real.exp b ≤ A.det) := by
  constructor
  · intro H
    have hpos := posDef_of_forall_log_det_le_trace hA b H
    refine ⟨hpos, ?_⟩
    have h := H A⁻¹ hpos.inv
    rw [Matrix.nonsing_inv_mul A
        ((Matrix.isUnit_iff_isUnit_det A).mp hpos.isUnit),
      Matrix.trace_one, Fintype.card_fin, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv, Real.log_inv] at h
    apply (Real.le_log_iff_exp_le hpos.det_pos).mp
    linarith
  · rintro ⟨hpos, hb⟩ J hJ
    obtain ⟨B, hB, hBB⟩ := exists_posDef_square hpos
    have hstar : star B = B := by
      rw [Matrix.star_eq_conjTranspose, hB.isHermitian.eq]
    have hM : (B * J * B).PosDef := by
      simpa only [hstar] using
        (Matrix.IsUnit.posDef_star_right_conjugate_iff hB.isUnit).mpr hJ
    have htr : (B * J * B).trace = (J * A).trace := by
      rw [Matrix.trace_mul_cycle, hBB, Matrix.trace_mul_comm]
    have hdet : (B * J * B).det = J.det * A.det := by
      rw [Matrix.det_mul, Matrix.det_mul, ← hBB, Matrix.det_mul]
      ring
    have h := log_det_add_card_le_trace hM
    rw [htr, hdet,
      Real.log_mul (ne_of_gt hJ.det_pos) (ne_of_gt hpos.det_pos)] at h
    have hlog := (Real.le_log_iff_exp_le hpos.det_pos).mpr hb
    linarith

end LogDetInf

section LogDetConcavity

private lemma scalar_log_gap {a b K : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haK : a ≤ K) (hbK : b ≤ K) :
    Real.log b + (b - a) ^ 2 / (2 * K ^ 2) ≤
      Real.log a + (b - a) / a := by
  let f : ℝ → ℝ := fun x => Real.log x + x ^ 2 / (2 * K ^ 2)
  let d : ℝ → ℝ := fun x => x⁻¹ + x / K ^ 2
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt f (d x) x := by
    intro x hx
    have h := (Real.hasDerivAt_log hx.ne').fun_add
      (((hasDerivAt_id x).fun_pow 2).div_const (2 * K ^ 2))
    have he :
        x⁻¹ + (↑(2 : ℕ) * id x ^ (2 - 1) * 1) / (2 * K ^ 2) = d x := by
      dsimp [d]
      ring
    rw [he] at h
    exact h
  have hdd :
      ∀ x : ℝ, 0 < x → HasDerivAt d (-1 / x ^ 2 + 1 / K ^ 2) x := by
    intro x hx
    simpa [d] using
      ((hasDerivAt_id x).inv hx.ne').fun_add
        ((hasDerivAt_id x).div_const (K ^ 2))
  have hc : ConcaveOn ℝ (Set.Ioc 0 K) f := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos
      (f' := d) (f'' := fun x => -1 / x ^ 2 + 1 / K ^ 2)
      (convex_Ioc 0 K)
      (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx).1).hasDerivWithinAt)
      (fun x hx => (hdd x (interior_subset hx).1).hasDerivWithinAt) ?_
    intro x hx
    have hx' : x ∈ Set.Ioc 0 K := interior_subset hx
    have hsq : x ^ 2 ≤ K ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hx'.2)
        (show 0 ≤ K + x by linarith [hx'.1, hx'.2])
      nlinarith
    have hi := one_div_le_one_div_of_le (sq_pos_of_pos hx'.1) hsq
    change -1 / x ^ 2 + 1 / K ^ 2 ≤ 0
    simp only [neg_div]
    linarith
  have ht : f b - f a ≤ d a * (b - a) := by
    rcases lt_trichotomy a b with hab | hab | hab
    · have hs := hc.slope_le_of_hasDerivAt
        ⟨ha, haK⟩ ⟨hb, hbK⟩ hab (hd a ha)
      rw [slope_def_field] at hs
      exact (div_le_iff₀ (sub_pos.mpr hab)).mp hs
    · subst b
      simp
    · have hs := hc.le_slope_of_hasDerivAt
        ⟨hb, hbK⟩ ⟨ha, haK⟩ hab (hd a ha)
      rw [slope_def_field] at hs
      have hs' := (le_div_iff₀ (sub_pos.mpr hab)).mp hs
      nlinarith
  have he :
      Real.log b + (b - a) ^ 2 / (2 * K ^ 2) -
          (Real.log a + (b - a) / a) =
        f b - f a - d a * (b - a) := by
    dsimp [f, d]
    ring
  linarith

private lemma bounded_spectral_decomposition {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hA : A.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      A = U * diagonal a * Uᵀ ∧
      (∀ i, 0 < a i) ∧ (∀ i, a i ≤ K) ∧
      Real.log A.det = ∑ i, Real.log (a i) := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  let a : Fin n → ℝ := hA.isHermitian.eigenvalues
  have hu : Uᵀ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hu' : U * Uᵀ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hA.isHermitian.eigenvectorUnitary
  have he : A = U * diagonal a * Uᵀ := by
    simpa [U, a, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hA.isHermitian.spectral_theorem
  have ha : ∀ i, 0 < a i := hA.eigenvalues_pos
  have hc : Uᵀ * A * U = diagonal a := by
    calc
      Uᵀ * A * U = (Uᵀ * U) * diagonal a * (Uᵀ * U) := by
        rw [he]
        simp only [Matrix.mul_assoc]
      _ = diagonal a := by rw [hu, one_mul, mul_one]
  have hk : ∀ i, a i ≤ K := by
    intro i
    have hh := hAK.conjTranspose_mul_mul_same U
    have hh' :
        Uᴴ * (K • 1 - A) * U = K • 1 - diagonal a := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        mul_one, hu, hc]
    rw [hh'] at hh
    have hv := hh.diag_nonneg (i := i)
    apply sub_nonneg.mp
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one, Matrix.diagonal_apply_eq] using hv
  refine ⟨U, a, hu, hu', he, ha, hk, ?_⟩
  have hdet : A.det = ∏ i, a i := by
    simpa [a] using hA.isHermitian.det_eq_prod_eigenvalues
  rw [hdet, Real.log_prod (fun i _ => (ha i).ne')]

private lemma trace_spectral_pair {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    ((U * diagonal a * Uᵀ) * (V * diagonal b * Vᵀ)).trace =
      ∑ i, ∑ j, a i * b j * (Uᵀ * V) i j ^ 2 := by
  calc
    ((U * diagonal a * Uᵀ) * (V * diagonal b * Vᵀ)).trace =
        (U * (diagonal a * Uᵀ * V * diagonal b * Vᵀ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((diagonal a * Uᵀ * V * diagonal b * Vᵀ) * U).trace :=
      Matrix.trace_mul_comm _ _
    _ = (diagonal a * (Uᵀ * V) * diagonal b * (Uᵀ * V)ᵀ).trace := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    _ = ∑ i, ∑ j, a i * b j * (Uᵀ * V) i j ^ 2 := by
      unfold Matrix.trace Matrix.diag
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
      ring

private lemma trace_spectral_square {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hu : Uᵀ * U = 1) :
    ((U * diagonal a * Uᵀ) * (U * diagonal a * Uᵀ)).trace =
      ∑ i, a i ^ 2 := by
  have hm :
      (U * diagonal a * Uᵀ) * (U * diagonal a * Uᵀ) =
        U * diagonal (fun i => a i ^ 2) * Uᵀ := by
    calc
      (U * diagonal a * Uᵀ) * (U * diagonal a * Uᵀ) =
          U * (diagonal a * (Uᵀ * U) * diagonal a) * Uᵀ := by
        simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => a i ^ 2) * Uᵀ := by
        simp only [hu, mul_one, Matrix.diagonal_mul_diagonal, pow_two]
  rw [hm, Matrix.trace_mul_cycle, hu, one_mul, Matrix.trace_diagonal]

private lemma inv_spectral {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    (hu : Uᵀ * U = 1) (hu' : U * Uᵀ = 1) (ha : ∀ i, 0 < a i) :
    (U * diagonal a * Uᵀ)⁻¹ =
      U * diagonal (fun i => (a i)⁻¹) * Uᵀ := by
  apply Matrix.inv_eq_left_inv
  have hd :
      diagonal (fun i => (a i)⁻¹ * a i) =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hv : (fun i => (a i)⁻¹ * a i) = fun _ => (1 : ℝ) :=
      funext fun i => inv_mul_cancel₀ (ha i).ne'
    rw [hv, Matrix.diagonal_one]
  calc
    (U * diagonal (fun i => (a i)⁻¹) * Uᵀ) * (U * diagonal a * Uᵀ) =
        U * (diagonal (fun i => (a i)⁻¹) * (Uᵀ * U) * diagonal a) * Uᵀ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hu, mul_one, Matrix.diagonal_mul_diagonal, hd, mul_one, hu']

private lemma orthogonal_row_sq {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q * Qᵀ = 1) (i : Fin n) :
    ∑ j, Q i j ^ 2 = 1 := by
  have hh := congrFun (congrFun hQ i) i
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← sq,
    Matrix.one_apply_eq] using hh

private lemma frobenius_sub_trace {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (∑ i, ∑ j, (B - A) i j ^ 2) =
      (B * B).trace + (A * A).trace - 2 * (A * B).trace := by
  have hd : (B - A)ᵀ = B - A := by
    rw [Matrix.transpose_sub, hB, hA]
  have ht :
      ((B - A) * (B - A)).trace = ∑ i, ∑ j, (B - A) i j ^ 2 := by
    unfold Matrix.trace Matrix.diag
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hij := congrFun (congrFun hd i) j
    change (B - A) j i = (B - A) i j at hij
    rw [hij]
    ring
  rw [← ht]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm B A]
  ring

/-- **Quantitative concavity of `log det`**: for positive definite `A, B ≤ K·Id`,
`log det B + ‖B − A‖²_F / (2K²) ≤ log det A + tr(A⁻¹ (B − A))`. -/
theorem log_det_add_frobenius_sq_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef) :
    Real.log B.det + (∑ i, ∑ j, (B - A) i j ^ 2) / (2 * K ^ 2) ≤
      Real.log A.det + (A⁻¹ * (B - A)).trace := by
  obtain ⟨U, a, hu, hu', hAd, ha, haK, hAlog⟩ :=
    bounded_spectral_decomposition hA hAK
  obtain ⟨V, b, hv, hv', hBd, hb, hbK, hBlog⟩ :=
    bounded_spectral_decomposition hB hBK
  let Q : Matrix (Fin n) (Fin n) ℝ := Uᵀ * V
  have hQr : Q * Qᵀ = 1 := by
    dsimp [Q]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Uᵀ * V * (Vᵀ * U) = Uᵀ * (V * Vᵀ) * U := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv', mul_one, hu]
  have hQc : Qᵀ * Q = 1 := by
    dsimp [Q]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      Vᵀ * U * (Uᵀ * V) = Vᵀ * (U * Uᵀ) * V := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu', mul_one, hv]
  have hr : ∀ i, ∑ j, Q i j ^ 2 = 1 :=
    orthogonal_row_sq Q hQr
  have hc : ∀ j, ∑ i, Q i j ^ 2 = 1 := by
    intro j
    have hh : Qᵀ * (Qᵀ)ᵀ = 1 := by
      rw [Matrix.transpose_transpose]
      exact hQc
    simpa only [Matrix.transpose_apply] using orthogonal_row_sq Qᵀ hh j
  have row_weight (f : Fin n → ℝ) :
      (∑ i, ∑ j, f i * Q i j ^ 2) = ∑ i, f i := by
    simp only [← Finset.mul_sum, hr, mul_one]
  have col_weight (f : Fin n → ℝ) :
      (∑ i, ∑ j, f j * Q i j ^ 2) = ∑ j, f j := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hc, mul_one]
  have hAA : (A * A).trace = ∑ i, a i ^ 2 := by
    rw [hAd]
    exact trace_spectral_square U a hu
  have hBB : (B * B).trace = ∑ j, b j ^ 2 := by
    rw [hBd]
    exact trace_spectral_square V b hv
  have hAB :
      (A * B).trace = ∑ i, ∑ j, a i * b j * Q i j ^ 2 := by
    rw [hAd, hBd]
    exact trace_spectral_pair U V a b
  have hAs : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hBs : Bᵀ = B := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.isHermitian.eq
  have hgap :
      (∑ i, ∑ j, (b j - a i) ^ 2 * Q i j ^ 2) =
        ∑ i, ∑ j, (B - A) i j ^ 2 := by
    calc
      (∑ i, ∑ j, (b j - a i) ^ 2 * Q i j ^ 2) =
          ∑ i, ∑ j,
            (b j ^ 2 * Q i j ^ 2 + a i ^ 2 * Q i j ^ 2 -
              2 * (a i * b j * Q i j ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ i, ∑ j, b j ^ 2 * Q i j ^ 2) +
          (∑ i, ∑ j, a i ^ 2 * Q i j ^ 2) -
          (∑ i, ∑ j, 2 * (a i * b j * Q i j ^ 2)) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ j, b j ^ 2) + (∑ i, a i ^ 2) -
          2 * (∑ i, ∑ j, a i * b j * Q i j ^ 2) := by
        rw [col_weight (fun j => b j ^ 2), row_weight (fun i => a i ^ 2)]
        simp only [← Finset.mul_sum]
      _ = (B * B).trace + (A * A).trace - 2 * (A * B).trace := by
        rw [hAA, hBB, hAB]
      _ = ∑ i, ∑ j, (B - A) i j ^ 2 :=
        (frobenius_sub_trace A B hAs hBs).symm
  have hAi :
      A⁻¹ = U * diagonal (fun i => (a i)⁻¹) * Uᵀ := by
    rw [hAd]
    exact inv_spectral U a hu hu' ha
  have hAiB :
      (A⁻¹ * B).trace = ∑ i, ∑ j, (a i)⁻¹ * b j * Q i j ^ 2 := by
    rw [hAi, hBd]
    exact trace_spectral_pair U V (fun i => (a i)⁻¹) b
  have hAiA : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hone :
      (∑ i, ∑ j, (1 : ℝ) * Q i j ^ 2) =
        (1 : Matrix (Fin n) (Fin n) ℝ).trace := by
    rw [row_weight (fun _ => (1 : ℝ))]
    simp
  have htangent :
      (∑ i, ∑ j, ((b j - a i) / a i) * Q i j ^ 2) =
        (A⁻¹ * (B - A)).trace := by
    calc
      (∑ i, ∑ j, ((b j - a i) / a i) * Q i j ^ 2) =
          ∑ i, ∑ j,
            ((a i)⁻¹ * b j * Q i j ^ 2 - 1 * Q i j ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        field_simp [(ha i).ne']
      _ = (∑ i, ∑ j, (a i)⁻¹ * b j * Q i j ^ 2) -
          (∑ i, ∑ j, (1 : ℝ) * Q i j ^ 2) := by
        simp only [Finset.sum_sub_distrib]
      _ = (A⁻¹ * B).trace - (1 : Matrix (Fin n) (Fin n) ℝ).trace := by
        rw [hAiB, hone]
      _ = (A⁻¹ * (B - A)).trace := by
        rw [Matrix.mul_sub, Matrix.trace_sub, hAiA]
  have hdiv :
      (∑ i, ∑ j, ((b j - a i) ^ 2 / (2 * K ^ 2)) * Q i j ^ 2) =
        (∑ i, ∑ j, (b j - a i) ^ 2 * Q i j ^ 2) / (2 * K ^ 2) := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs :
      (∑ i, ∑ j,
        (Real.log (b j) + (b j - a i) ^ 2 / (2 * K ^ 2)) * Q i j ^ 2) ≤
      ∑ i, ∑ j,
        (Real.log (a i) + (b j - a i) / a i) * Q i j ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right
      (scalar_log_gap (ha i) (hb j) (haK i) (hbK j))
      (sq_nonneg (Q i j))
  simp only [add_mul, Finset.sum_add_distrib] at hs
  rw [col_weight (fun j => Real.log (b j)),
    row_weight (fun i => Real.log (a i)),
    hdiv, hgap, htangent, ← hBlog, ← hAlog] at hs
  exact hs

end LogDetConcavity

end FunctionalInequalities.Analysis

/-! ## Directional deficits in a fixed rank-one frame -/

section FrameDeficit

open Matrix Finset

namespace FunctionalInequalities.Analysis

/--
A finite weighted comparison `∑ b_j d_j ≤ ∑ b_j c_j + E` with coefficients `lc ≤ b_j ≤ uc` (`0 ≤
lc`) and nonnegative
deficits bounds every single deficit: `lc · d_k ≤ uc · ∑ c_j + E`. -/
theorem deficit_le_sum_of_weighted_comparison {N : ℕ} (b dx dy : Fin N → ℝ) {lc uc E : ℝ}
    (hlc : 0 ≤ lc) (hb : ∀ j, lc ≤ b j ∧ b j ≤ uc) (hdx : ∀ j, 0 ≤ dx j) (hdy : ∀ j, 0 ≤ dy j)
    (hcomp : ∑ j, b j * dy j ≤ (∑ j, b j * dx j) + E) (k : Fin N) :
    lc * dy k ≤ uc * (∑ j, dx j) + E := by
  calc
    _ ≤ b k * dy k := mul_le_mul_of_nonneg_right (hb k).1 (hdy k)
    _ ≤ ∑ j, b j * dy j :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hlc.trans (hb j).1) (hdy j)) (mem_univ k)
    _ ≤ (∑ j, b j * dx j) + E := hcomp
    _ ≤ (∑ j, uc * dx j) + E :=
      add_le_add (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hb j).2 (hdx j))
        le_rfl
    _ = _ := by rw [Finset.mul_sum]

private theorem trace_rank_one_mul {n : ℕ} (v : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    (vecMulVec v v * H).trace = ∑ i, ∑ j, v i * v j * H i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/--
Directional deficits of two positive definite matrices `X, Y ≤ K·I` in a fixed rank-one frame. If
`ρ X⁻¹ = ∑ b_j γ_j γ_jᵀ` with `lc ≤ b_j ≤ uc` (`ρ, lc ≥ 0`), the directional quadratic forms are
capped by `M_j`, and
`ρ (log det X − log det Y) ≤ E`, then `lc (M_k − γ_kᵀ Y γ_k) ≤ uc ∑_j (M_j − γ_jᵀ X γ_j) + E`. The
proof is the
log-determinant supporting plane `log_det_add_frobenius_sq_le` (the comparison step of
Gilbarg–Trudinger (2001), §17.4). -/
theorem directional_deficit_le_sum_of_logdet {n N : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ)
    (γ : Fin N → Fin n → ℝ) (b M : Fin N → ℝ) {K ρ lc uc E : ℝ} (hX : X.PosDef) (hY : Y.PosDef)
    (hXK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - X).PosSemidef)
    (hYK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Y).PosSemidef) (hρ : 0 ≤ ρ) (hlc : 0 ≤ lc)
    (hb : ∀ j, lc ≤ b j ∧ b j ≤ uc) (hframe : ρ • X⁻¹ = ∑ j, b j • vecMulVec (γ j) (γ j))
    (hMX : ∀ j, (∑ i, ∑ a, γ j i * γ j a * X i a) ≤ M j)
    (hMY : ∀ j, (∑ i, ∑ a, γ j i * γ j a * Y i a) ≤ M j)
    (hE : ρ * (Real.log X.det - Real.log Y.det) ≤ E) (k : Fin N) :
    lc * (M k - ∑ i, ∑ a, γ k i * γ k a * Y i a) ≤
      uc * (∑ j, (M j - ∑ i, ∑ a, γ j i * γ j a * X i a)) + E := by
  let dx := fun j => M j - ∑ i, ∑ a, γ j i * γ j a * X i a
  let dy := fun j => M j - ∑ i, ∑ a, γ j i * γ j a * Y i a
  have hq : 0 ≤ (∑ i, ∑ j, (Y - X) i j ^ 2) / (2 * K ^ 2) := by positivity
  have hconc := log_det_add_frobenius_sq_le hX hY hXK hYK
  have hplane : ρ * (Real.log Y.det - Real.log X.det) ≤ ((ρ • X⁻¹) * (Y - X)).trace := by
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [hconc]) hρ
  have htr : ((ρ • X⁻¹) * (Y - X)).trace = (∑ j, b j * dx j) - ∑ j, b j * dy j := by
    rw [hframe, Finset.sum_mul, Matrix.trace_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_rank_one_mul]
    dsimp only [dx, dy]
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [htr] at hplane
  have hcomp : (∑ j, b j * dy j) ≤ (∑ j, b j * dx j) + E := by nlinarith
  exact
    deficit_le_sum_of_weighted_comparison b dx dy hlc hb (fun j => sub_nonneg.mpr (hMX j))
      (fun j => sub_nonneg.mpr (hMY j)) hcomp k

end FunctionalInequalities.Analysis

end FrameDeficit

namespace FunctionalInequalities.Analysis

/-- **Three-point log-det concavity**: for positive definite `A, B₊, B₋ ≤ K·Id`,
`(‖B₊ − A‖²_F + ‖B₋ − A‖²_F)/(2K²) ≤ tr(A⁻¹(B₊ + B₋ − 2A)) − log det B₊ − log det B₋ + 2 log det A`.
-/
theorem frobenius_add_frobenius_le_trace_sub_log_det {n : ℕ}
    {A Bp Bm : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hA : A.PosDef) (hBp : Bp.PosDef)
    (hBm : Bm.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBpK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Bp).PosSemidef)
    (hBmK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - Bm).PosSemidef) :
    ((∑ i, ∑ j, (Bp - A) i j ^ 2) + ∑ i, ∑ j, (Bm - A) i j ^ 2) / (2 * K ^ 2) ≤
      (A⁻¹ * (Bp + Bm - 2 • A)).trace - Real.log Bp.det - Real.log Bm.det +
        2 * Real.log A.det := by
  have hp := log_det_add_frobenius_sq_le hA hBp hAK hBpK
  have hm := log_det_add_frobenius_sq_le hA hBm hAK hBmK
  have he : Bp + Bm - 2 • A = (Bp - A) + (Bm - A) := by
    rw [two_smul]
    abel
  rw [he, Matrix.mul_add, Matrix.trace_add, add_div]
  linarith


end FunctionalInequalities.Analysis
