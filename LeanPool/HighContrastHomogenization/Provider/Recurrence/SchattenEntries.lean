/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSpectral
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# High-contrast homogenization: Provider.Recurrence.SchattenEntries

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Entries, traces and the Schatten size

The scalarization of the fixed-grid estimates rests on three comparisons
between the Schatten size `|H|_{S_Q}` of a symmetric doubled block and the
scalar data of its entries.

*The entrywise bound* `|H_{ab}| ≤ |H|_{S_Q}` is the step that turns a matrix
estimate into `4d²` scalar estimates in `l.fixed.geometry.matrix.averaging`.
Its content is that a single entry of a symmetric matrix is dominated by the
largest eigenvalue in absolute value, which in turn is dominated by the
`ℓ^Q`-size of the whole spectrum.

*The Hilbert–Schmidt comparison* `|H|_{S_Q} ≤ (Σ_{a,b} H_{ab}²)^{1/2}` for
`Q ≥ 2` is the first half of the scalarization display of the same lemma.  It
is the `ℓ^Q ⊆ ℓ^2` embedding on the spectrum, read through the identity
`Σ_i λ_i² = tr(H²) = Σ_{a,b} H_{ab}²`.

*The trace comparison* `tr D ≤ m^{1-1/Q}|D|_{S_Q}` for `D ≥ 0` is the step of
`l.fixed.geometry.positive.gap` that converts the trace produced by the positivity
argument into the Schatten size the conclusion is stated in.  It is Hölder's
inequality against the constant function on the `m` eigenvalues; here
`m = 2d` is the size of a doubled block.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Schatten trace of a symmetric matrix -/

/-- **The spectral form of the Schatten trace.**  The Schatten size squares its
argument before applying the power `Q/2`; on the spectrum this composition is
`(x²)^{Q/2} = |x|^Q`, so the trace it takes is the `ℓ^Q`-sum of the eigenvalues
in absolute value.  No positivity is needed: the absolute value is what the
squaring leaves behind. -/
theorem trace_cfc_rpow_mul_self_eq_sum_abs_rpow {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : ℝ} (hQ : 0 < Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ (Q / 2)) (A * A)) = ∑ i, |hA.eigenvalues i| ^ Q := by
  have hsa : IsSelfAdjoint A := hA
  have hsq : cfc (fun x : ℝ => x ^ (2 : ℕ)) A = A * A := by
    have h1 := cfc_pow (R := ℝ) (fun x : ℝ => x) 2 A
    rw [cfc_id' ℝ A hsa] at h1
    rw [h1, pow_two]
  have hcont : ContinuousOn (fun x : ℝ => x ^ (Q / 2))
      ((fun x : ℝ => x ^ (2 : ℕ)) '' spectrum ℝ A) := fun x _ =>
    (Real.continuousAt_rpow_const x (Q / 2) (Or.inr (by linarith only [hQ]))).continuousWithinAt
  have hcomp : cfc ((fun x : ℝ => x ^ (Q / 2)) ∘ fun x : ℝ => x ^ (2 : ℕ)) A
      = cfc (fun x : ℝ => x ^ (Q / 2)) (A * A) := by
    rw [cfc_comp (R := ℝ) (fun x : ℝ => x ^ (Q / 2)) (fun x : ℝ => x ^ (2 : ℕ)) A hsa hcont, hsq]
  have hcongr : cfc ((fun x : ℝ => x ^ (Q / 2)) ∘ fun x : ℝ => x ^ (2 : ℕ)) A
      = cfc (fun x : ℝ => |x| ^ Q) A := by
    refine cfc_congr (R := ℝ) fun x _ => ?_
    have hnat : (x ^ (2 : ℕ) : ℝ) = |x| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    simp only [Function.comp_apply, hnat]
    rw [← Real.rpow_mul (abs_nonneg x)]
    congr 1
    ring
  rw [← hcomp, hcongr, trace_cfc_eq_sum_eigenvalues hA]

/-! ## The entrywise bound -/

/-- An entry of a matrix conjugated from a diagonal one by a matrix with
orthonormal rows is bounded by the largest diagonal entry in absolute value.
Cauchy–Schwarz appears in the elementary form `2|x||y| ≤ x² + y²`, and the two
row sums are `1`. -/
private theorem abs_conj_diagonal_apply_le {U : Matrix n n ℝ} (hU : U * Uᴴ = 1) {v : n → ℝ}
    {t : ℝ} (ht : 0 ≤ t) (hv : ∀ i, |v i| ≤ t) (α β : n) :
    |(U * Matrix.diagonal v * Uᴴ) α β| ≤ t := by
  have hrow : ∀ γ : n, ∑ i, U γ i * U γ i = 1 := by
    intro γ
    calc ∑ i, U γ i * U γ i = ∑ i, U γ i * Uᴴ i γ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Matrix.conjTranspose_apply, star_trivial]
      _ = (U * Uᴴ) γ γ := Matrix.mul_apply.symm
      _ = 1 := by rw [hU, Matrix.one_apply_eq]
  have hentry : (U * Matrix.diagonal v * Uᴴ) α β = ∑ i, U α i * v i * U β i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial]
  have hbound : ∀ i : n, |U α i * v i * U β i| ≤ t * ((U α i * U α i + U β i * U β i) / 2) := by
    intro i
    have hcs : |U α i| * |U β i| ≤ (U α i * U α i + U β i * U β i) / 2 := by
      have hsq := two_mul_le_add_sq |U α i| |U β i|
      rw [sq_abs, sq_abs, pow_two, pow_two] at hsq
      linarith only [hsq]
    calc |U α i * v i * U β i| = |U α i| * |v i| * |U β i| := by rw [abs_mul, abs_mul]
      _ ≤ |U α i| * t * |U β i| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)) (abs_nonneg _)
      _ = t * (|U α i| * |U β i|) := by ring
      _ ≤ t * ((U α i * U α i + U β i * U β i) / 2) := mul_le_mul_of_nonneg_left hcs ht
  rw [hentry]
  calc |∑ i, U α i * v i * U β i| ≤ ∑ i, |U α i * v i * U β i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, t * ((U α i * U α i + U β i * U β i) / 2) := Finset.sum_le_sum fun i _ => hbound i
    _ = t := by
        have hsplit : ∀ i : n, t * ((U α i * U α i + U β i * U β i) / 2)
            = t / 2 * (U α i * U α i) + t / 2 * (U β i * U β i) := fun i => by ring
        rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hrow α, hrow β]
        ring

/-- **A spectral bound is an entrywise bound.**  Every entry of a symmetric
matrix is bounded by any bound on the absolute values of its eigenvalues. -/
theorem abs_apply_le_of_abs_eigenvalues_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {t : ℝ}
    (ht : 0 ≤ t) (h : ∀ i, |hA.eigenvalues i| ≤ t) (α β : n) : |A α β| ≤ t := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal hA.eigenvalues * (hA.eigenvectorUnitary : Matrix n n ℝ)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [hspec]
  exact abs_conj_diagonal_apply_le hU ht h α β

/-! ## The Hilbert–Schmidt trace -/

omit [DecidableEq n] in
/-- The trace of the square of a symmetric matrix is the sum of the squares of
its entries: this is the Hilbert–Schmidt norm in the two forms the
scalarization display compares. -/
theorem trace_mul_self_eq_sum_sq {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ α, ∑ β, A α β ^ 2 := by
  have hsymm : ∀ i j : n, A j i = A i j := fun i j => by
    simpa using hA.apply i j
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hsymm α β, pow_two]

/-! ## The trace–Schatten comparison -/

omit [DecidableEq n] in
/-- Hölder's inequality against the constant function: a sum of `m`
nonnegative reals is at most `m^{1-1/Q}` times their `ℓ^Q`-size. -/
private theorem sum_le_card_rpow_mul_rpow_sum [Nonempty n] {f : n → ℝ} (hf : ∀ i, 0 ≤ f i)
    {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ i, f i ≤ (Fintype.card n : ℝ) ^ (1 - Q⁻¹) * (∑ i, f i ^ Q) ^ Q⁻¹ := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hm : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hminv : (0 : ℝ) ≤ ((Fintype.card n : ℝ))⁻¹ := inv_nonneg.mpr hm.le
  have hS : (0 : ℝ) ≤ ∑ i, f i := Finset.sum_nonneg fun i _ => hf i
  have hT : (0 : ℝ) ≤ ∑ i, f i ^ Q := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) Q
  have hw : ∑ _i : n, ((Fintype.card n : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hm)]
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ : n => ((Fintype.card n : ℝ))⁻¹) f (fun _ _ => hminv) hw (fun i _ => hf i) hQ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hmean
  have hstep := Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hminv hS) Q) hmean
    (inv_nonneg.mpr hQ0.le)
  rw [← Real.rpow_mul (mul_nonneg hminv hS), mul_inv_cancel₀ (ne_of_gt hQ0), Real.rpow_one,
    Real.mul_rpow hminv hT] at hstep
  have hfinal : ((Fintype.card n : ℝ)) ^ (1 - Q⁻¹)
      = (Fintype.card n : ℝ) * (((Fintype.card n : ℝ))⁻¹) ^ Q⁻¹ := by
    rw [Real.inv_rpow hm.le, ← Real.rpow_neg hm.le, sub_eq_add_neg, Real.rpow_add hm,
      Real.rpow_one]
  rw [hfinal, mul_assoc]
  have hmul := mul_le_mul_of_nonneg_left hstep hm.le
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hm), one_mul] at hmul

/-- **The trace comparison of `l.fixed.geometry.positive.gap`** at the level of a general
positive semidefinite matrix: `tr D ≤ m^{1-1/Q}(tr(D^Q))^{1/Q}`. -/
theorem trace_le_card_rpow_mul_rpow_trace_cfc_rpow [Nonempty n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {Q : ℝ} (hQ : 1 ≤ Q) :
    Matrix.trace A ≤ (Fintype.card n : ℝ) ^ (1 - Q⁻¹) *
      Matrix.trace (cfc (fun x : ℝ => x ^ Q) A) ^ Q⁻¹ := by
  have hsum : Matrix.trace A = ∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  rw [hsum, trace_cfc_eq_sum_eigenvalues hA.isHermitian]
  exact sum_le_card_rpow_mul_rpow_sum hA.eigenvalues_nonneg hQ

/-! ## The three comparisons for a doubled block -/

section Block

variable {d : ℕ}

/-- The Schatten size of a symmetric doubled block is the `ℓ^Q`-size of its
spectrum. -/
theorem schattenNorm_eq_rpow_sum_abs_rpow {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    {Q : ℝ} (hQ : 0 < Q) :
    schattenNorm Q H = (∑ i, |(isHermitian_toFullBlockMat hH).eigenvalues i| ^ Q) ^ Q⁻¹ := by
  simp only [schattenNorm]
  rw [trace_cfc_rpow_mul_self_eq_sum_abs_rpow (isHermitian_toFullBlockMat hH) hQ]

/-- **The entrywise bound `|H_{ab}| ≤ |H|_{S_Q}`** of
`l.fixed.geometry.matrix.averaging`.  Each eigenvalue is dominated by the
`ℓ^Q`-size of the spectrum, and a spectral bound is an entrywise bound. -/
theorem abs_toFullBlockMat_le_schattenNorm {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    {Q : ℝ} (hQ : 0 < Q) (α β : BlockCoord d) :
    |toFullBlockMat H α β| ≤ schattenNorm Q H := by
  have hherm := isHermitian_toFullBlockMat hH
  have hval := schattenNorm_eq_rpow_sum_abs_rpow hH hQ
  refine abs_apply_le_of_abs_eigenvalues_le hherm (zero_le_schattenNorm hH Q) (fun i => ?_) α β
  have hle : |hherm.eigenvalues i| ^ Q ≤ ∑ j, |hherm.eigenvalues j| ^ Q :=
    Finset.single_le_sum (f := fun j => |hherm.eigenvalues j| ^ Q)
      (fun j _ => Real.rpow_nonneg (abs_nonneg _) Q) (Finset.mem_univ i)
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) Q) hle
    (inv_nonneg.mpr hQ.le)
  rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ (ne_of_gt hQ), Real.rpow_one] at hroot
  rw [hval]
  exact hroot

/-- **The Hilbert–Schmidt comparison** `|H|_{S_Q} ≤ (Σ_{a,b}H_{ab}²)^{1/2}` for
`Q ≥ 2`, the matrix half of the scalarization display of
`l.fixed.geometry.matrix.averaging`.  The trace-power estimate applied to
`H²` at the exponent `Q/2` gives `tr((H²)^{Q/2}) ≤ (tr H²)^{Q/2}`, and
`tr H² = Σ_{a,b}H_{ab}²`. -/
theorem schattenNorm_le_sum_sq_rpow {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    {Q : ℝ} (hQ : 2 ≤ Q) :
    schattenNorm Q H ≤ (∑ α, ∑ β, toFullBlockMat H α β ^ 2) ^ (2⁻¹ : ℝ) := by
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hQ2 : (1 : ℝ) ≤ Q / 2 := by linarith only [hQ]
  have hherm := isHermitian_toFullBlockMat hH
  have hsq : (toFullBlockMat H * toFullBlockMat H).PosSemidef := by
    have hps := Matrix.posSemidef_conjTranspose_mul_self (toFullBlockMat H)
    rwa [(hherm : (toFullBlockMat H).IsHermitian)] at hps
  have hT : (0 : ℝ) ≤ Matrix.trace (toFullBlockMat H * toFullBlockMat H) := hsq.trace_nonneg
  have hsplit : Matrix.trace (toFullBlockMat H * toFullBlockMat H) ^ (Q / 2 - 1) *
      Matrix.trace (toFullBlockMat H * toFullBlockMat H)
      = Matrix.trace (toFullBlockMat H * toFullBlockMat H) ^ (Q / 2) := by
    rcases eq_or_lt_of_le hT with hzero | hposT
    · rw [← hzero, mul_zero, Real.zero_rpow (by linarith only [hQ2] : Q / 2 ≠ 0)]
    · have hadd := Real.rpow_add hposT (Q / 2 - 1) 1
      rw [Real.rpow_one] at hadd
      rw [← hadd]
      norm_num
  have hstep := trace_cfc_rpow_le_mul_trace hsq (le_trace_smul_one hsq) hQ2
  rw [hsplit] at hstep
  have hroot := Real.rpow_le_rpow (zero_le_trace_cfc_rpow hsq (Q / 2)) hstep
    (inv_nonneg.mpr hQ0.le)
  rw [← Real.rpow_mul hT] at hroot
  have hexp : Q / 2 * Q⁻¹ = 2⁻¹ := by
    field_simp
  rw [hexp, trace_mul_self_eq_sum_sq hherm] at hroot
  exact hroot

/-- **The trace comparison `tr D ≤ m^{1-1/Q}|D|_{S_Q}`** of
`l.fixed.geometry.positive.gap`, for a positive doubled block: the matrix size `m` of a
doubled block is `2d`, and the hypothesis `0 < d` is the lemma's `m ≥ 1`. -/
theorem blockTrace_le_card_rpow_mul_schattenNorm {H : BlockMat d} (hd : 0 < d)
    (hpos : (toFullBlockMat H).PosSemidef) {Q : ℝ} (hQ : 1 ≤ Q) :
    blockTrace H ≤ (2 * d : ℝ) ^ (1 - Q⁻¹) * schattenNorm Q H := by
  have : Nonempty (BlockCoord d) := ⟨Sum.inl ⟨0, hd⟩⟩
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * d := by
    simp [BlockCoord, Fintype.card_sum, two_mul]
  have hval : schattenNorm Q H
      = Matrix.trace (cfc (fun x : ℝ => x ^ Q) (toFullBlockMat H)) ^ Q⁻¹ := by
    simp only [schattenNorm]
    rw [trace_cfc_rpow_mul_self hpos hQ0]
  have h := trace_le_card_rpow_mul_rpow_trace_cfc_rpow hpos hQ
  rw [hcard] at h
  rw [blockTrace, hval]
  exact h

end Block

end

end Recurrence
end HighContrast
end HCPolySupport
