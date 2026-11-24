/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MinkowskiDeterminant

/-!
# The determinant as an infimum of traces

Blueprint `ana:determinant-trace-inf` (`blueprint/src/analytic.tex`; TN.5, toward
    `ana:volume-semicontinuity`: the
identification of the infimum functional of `ana:ac-density-liminf` with `det^{1/n}`).  Source:
    the arithmetic-geometric mean
inequality, as used by Boucksom 2002 (`bou02-volume`) for the concavity of `det^{1/n}` (arXiv
    Lemma 3.5).

For positive semidefinite Hermitian complex matrices of size `n ≥ 1` (indexed by a nonempty finite
    type), with real
determinants and traces:

* `rpow_inv_card_re_det_le_re_trace_div`: `(det X)^{1/n} ≤ tr X / n` (AM-GM on the eigenvalues);
* `rpow_inv_card_re_det_mul_le`: `(det A)^{1/n} (det B)^{1/n} ≤ tr (B A) / n` (apply it to
    `y A y*`, `B = y* y`);
* `exists_posDef_det_eq_one_re_trace_div_le`: for every `ε > 0` some positive definite `B` with
    `det B = 1` has
  `tr (B A) / n ≤ (det A)^{1/n} + ε` (take `B = (det A_t)^{1/n} A_t⁻¹`, `A_t = A + t`, `t` small);
* `isGLB_re_trace_div`: **`(det A)^{1/n}` is the infimum of `tr (B A) / n` over the positive
    definite `B` with `det B = 1`.**

Generic matrix analysis: no complex-geometric, pluripotential, Kähler, volume or current constant.
    Sorry-free.
-/

@[expose] public section

open Finset Matrix Filter
open scoped ComplexOrder MatrixOrder Topology

namespace SGPT.Foundations.Analysis.Pending.DeterminantTraceInf

open MinkowskiDeterminant

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of a Hermitian matrix is the (real) sum of its eigenvalues. -/
theorem re_trace_eq_sum_eigenvalues {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X.trace.re = ∑ i, hX.eigenvalues i := by
  rw [hX.trace_eq_sum_eigenvalues]
  simp

/-- **AM-GM for matrices**: `(det X)^{1/n} ≤ tr X / n` for a positive semidefinite `X` of size
    `n ≥ 1`. -/
theorem rpow_inv_card_re_det_le_re_trace_div [Nonempty ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) :
    X.det.re ^ ((Fintype.card ι : ℝ)⁻¹) ≤ X.trace.re / Fintype.card ι := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hl : ∀ i, 0 ≤ hX.isHermitian.eigenvalues i := hX.eigenvalues_nonneg
  have hw : ∑ _i : ι, n⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn, mul_inv_cancel₀ hn0.ne']
  have h := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) (fun _ => n⁻¹)
    (fun i => hX.isHermitian.eigenvalues i) (fun _ _ => (inv_nonneg.mpr hn0.le))
      hw (fun i _ => hl i)
  rw [det_eq_ofReal_prod_eigenvalues hX.isHermitian, Complex.ofReal_re,
    re_trace_eq_sum_eigenvalues hX.isHermitian,
    ← Real.finsetProd_rpow _ _ fun i _ => hl i]
  calc ∏ i, hX.isHermitian.eigenvalues i ^ n⁻¹ ≤ ∑ i, n⁻¹ * hX.isHermitian.eigenvalues i := h
    _ = (∑ i, hX.isHermitian.eigenvalues i) / n := by rw [← Finset.mul_sum, inv_mul_eq_div]

omit [DecidableEq ι] in
/-- The trace of the product of two positive semidefinite matrices is a nonnegative real. -/
theorem re_trace_mul_nonneg {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (B * A).trace.re := by
  classical
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [Matrix.star_eq_conjTranspose]
  have hX : (y * A * yᴴ).PosSemidef := hA.mul_mul_conjTranspose_same y
  have htr : (yᴴ * y * A).trace = (y * A * yᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [htr, re_trace_eq_sum_eigenvalues hX.isHermitian]
  exact Finset.sum_nonneg fun i _ => hX.eigenvalues_nonneg i

/-- **`(det A)^{1/n} (det B)^{1/n} ≤ tr (B A) / n`** for positive semidefinite `A`,
    `B` of size `n ≥ 1`. -/
theorem rpow_inv_card_re_det_mul_le [Nonempty ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) * B.det.re ^ ((Fintype.card ι : ℝ)⁻¹) ≤
      (B * A).trace.re / Fintype.card ι := by
  have hBA := re_trace_mul_nonneg hA hB
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hB hBA ⊢
  set X := y * A * yᴴ with hXdef
  have hX : X.PosSemidef := hA.mul_mul_conjTranspose_same y
  have htr : (yᴴ * y * A).trace = X.trace := by
    rw [hXdef, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have hdet : X.det.re = A.det.re * (yᴴ * y).det.re := by
    have h1 : X.det = A.det * (yᴴ * y).det := by
      simp only [hXdef, Matrix.det_mul, Matrix.det_conjTranspose]
      ring
    rw [h1, det_eq_ofReal_re hA.isHermitian, det_eq_ofReal_re hB.isHermitian, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  rw [htr, ← Real.mul_rpow (re_det_nonneg hA) (re_det_nonneg hB), ← hdet]
  exact rpow_inv_card_re_det_le_re_trace_div hX

omit [Fintype ι] in
/-- `A + t` is positive definite for `A` positive semidefinite and `t > 0`. -/
theorem posDef_add_smul_one {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul (by exact_mod_cast ht))

/-- **Approximate minimizers**: for `ε > 0` there is a positive definite `B` with `det B = 1` and
`tr (B A) / n ≤ (det A)^{1/n} + ε`. -/
theorem exists_posDef_det_eq_one_re_trace_div_le [Nonempty ι] {A : Matrix ι ι ℂ} (hA :
    A.PosSemidef) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ B : Matrix ι ι ℂ, B.PosDef ∧ B.det = 1 ∧
      (B * A).trace.re / Fintype.card ι ≤ A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) + ε := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  set At : ℝ → Matrix ι ι ℂ := fun t => A + (t : ℂ) • (1 : Matrix ι ι ℂ) with hAt
  -- `t ↦ (det A_t)^{1/n}` is continuous at `0`
  have hcont : Continuous fun t : ℝ => (At t).det.re ^ n⁻¹ := by
    have h1 : Continuous fun t : ℝ => (At t).det := by
      refine Continuous.matrix_det ?_
      exact continuous_const.add (Continuous.smul (Complex.continuous_ofReal) continuous_const)
    refine (Complex.continuous_re.comp h1).rpow_const fun t => Or.inr (inv_nonneg.mpr hn0.le)
  have hlim : Tendsto (fun t : ℝ => (At t).det.re ^ n⁻¹) (𝓝[>] 0) (𝓝 (A.det.re ^ n⁻¹)) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa [hAt] using this
  obtain ⟨t, ht, ht0⟩ := ((hlim.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))).and
    self_mem_nhdsWithin).exists
  have ht0' : 0 < t := ht0
  have hPD : (At t).PosDef := posDef_add_smul_one hA ht0'
  set d : ℝ := (At t).det.re with hd
  have hd0 : 0 < d := by
    rw [hd, det_eq_ofReal_prod_eigenvalues hPD.isHermitian, Complex.ofReal_re]
    exact Finset.prod_pos fun i _ => hPD.eigenvalues_pos i
  have hdetC : (At t).det = (d : ℂ) := det_eq_ofReal_re hPD.isHermitian
  set c : ℝ := d ^ n⁻¹ with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hd0 _
  have hcn : c ^ Fintype.card ι = d := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hd0.le, ← hn, inv_mul_cancel₀ hn0.ne',
      Real.rpow_one]
  have hunit : IsUnit (At t).det := by rw [hdetC]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast
    hd0.ne')
  refine ⟨(c : ℂ) • (At t)⁻¹, hPD.inv.smul (by exact_mod_cast hc0), ?_, ?_⟩
  · rw [Matrix.det_smul, Matrix.det_nonsing_inv, hdetC, ← Complex.ofReal_pow, hcn,
    Ring.inverse_eq_inv',
      mul_inv_cancel₀ (by exact_mod_cast hd0.ne')]
  · -- `tr (A_t⁻¹ A) ≤ tr (A_t⁻¹ A_t) = n`
    have hinv : (At t)⁻¹ * At t = 1 := Matrix.nonsing_inv_mul _ hunit
    have hsplit : (At t)⁻¹ * A = 1 - (t : ℂ) • (At t)⁻¹ := by
      have : (At t)⁻¹ * A = (At t)⁻¹ * At t - (t : ℂ) • (At t)⁻¹ := by
        simp only [hAt, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, add_sub_cancel_right]
      rw [this, hinv]
    have htrinv : 0 ≤ ((At t)⁻¹).trace.re := by
      rw [re_trace_eq_sum_eigenvalues hPD.inv.isHermitian]
      exact Finset.sum_nonneg fun i _ => hPD.inv.posSemidef.eigenvalues_nonneg i
    have htr : ((At t)⁻¹ * A).trace.re ≤ n := by
      rw [hsplit, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Complex.sub_re,
        smul_eq_mul,
        Complex.re_ofReal_mul, Complex.natCast_re, ← hn]
      linarith [mul_nonneg ht0'.le htrinv]
    have hmul : ((c : ℂ) • (At t)⁻¹ * A).trace.re = c * ((At t)⁻¹ * A).trace.re := by
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rw [hmul, mul_div_assoc]
    calc c * (((At t)⁻¹ * A).trace.re / n) ≤ c * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hc0.le
          rw [div_le_one hn0]
          exact htr
      _ = c := mul_one c
      _ ≤ A.det.re ^ n⁻¹ + ε := ht.le

/-- **The determinant as an infimum of traces**: for a positive semidefinite Hermitian `A` of size
    `n ≥ 1`,
`(det A)^{1/n}` is the greatest lower bound of `tr (B A) / n` over the positive definite `B` with
    `det B = 1`. -/
theorem isGLB_re_trace_div [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    IsGLB {s : ℝ | ∃ B : Matrix ι ι ℂ, B.PosDef ∧ B.det = 1 ∧ s = (B * A).trace.re / Fintype.card
      ι}
      (A.det.re ^ ((Fintype.card ι : ℝ)⁻¹)) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro s ⟨B, hB, hdet, rfl⟩
    have h := rpow_inv_card_re_det_mul_le hA hB.posSemidef
    rwa [hdet, Complex.one_re, Real.one_rpow, mul_one] at h
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨B, hB, hdet, hle⟩ := exists_posDef_det_eq_one_re_trace_div_le hA (half_pos hε)
    calc b ≤ (B * A).trace.re / Fintype.card ι := hb ⟨B, hB, hdet, rfl⟩
      _ ≤ A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) + ε / 2 := hle
      _ < A.det.re ^ ((Fintype.card ι : ℝ)⁻¹) + ε := by linarith

end

end SGPT.Foundations.Analysis.Pending.DeterminantTraceInf
