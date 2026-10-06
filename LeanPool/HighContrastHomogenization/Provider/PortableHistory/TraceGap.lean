/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.DetOrder
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.MeanOrder

/-!
# High-contrast homogenization: Provider.PortableHistory.TraceGap

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The trace gap of a relative mean under a change of normalization

`p.fixed.geometry.one.grid.propagation` records the effect of changing the terminal
normalization on the nonlinear history.  For scales `j ≤ s ≤ t` the relative
means satisfy `P_{j,t} = R^t P_{j,s} R` with `R^t R = P_{s,t}`, and the printed
step is

`1 + tr(P_{j,t} - I) ≤ (1 + tr(P_{j,s} - I))(1 + tr(P_{s,t} - I))`,

obtained from "cyclicity and positivity of the trace".  The two ingredients are
proved here at the level of an arbitrary square matrix.

*Positivity of the trace of a product.*  For positive semidefinite `X` and `B`,
`tr(XB) ≥ 0`: writing `X = X^{1/2}X^{1/2}` and using cyclicity turns the product
into the congruence `X^{1/2}BX^{1/2}`, which is positive semidefinite.  Applied
to `B = ‖M‖I - M` it gives the comparison `tr(XM) ≤ ‖M‖tr(X)`.

*The spectral size of the congruence.*  The conjugation `X ↦ R^t X R` is
controlled by `‖RR^t‖`, which is `‖R‖²` and hence equals `‖R^tR‖`; the printed
step reads that norm off the Loewner bound `R^tR ≤ (1 + tr(P_{s,t} - I))I`,
which is in turn the elementary fact that a matrix above the identity has
spectral size at most one plus its trace gap — its largest eigenvalue exceeds
one by at most the sum of all the excesses.
-/

namespace HCPolySupport
namespace HighContrast
namespace PortableHistory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A matrix above the identity: spectral size against trace gap -/

/-- The trace gap of a matrix above the identity is the sum of the excesses of
its eigenvalues, and is nonnegative. -/
theorem trace_sub_one_nonneg {A : Matrix n n ℝ} (h : 1 ≤ A) :
    0 ≤ Matrix.trace (A - 1) := by
  have hPS : ((A : Matrix n n ℝ) - 1).PosSemidef := Matrix.le_iff.mp h
  exact hPS.trace_nonneg

/-- **The spectral size of a matrix above the identity is at most one plus its
trace gap.**  All the eigenvalues exceed one, so the largest of them exceeds one
by at most the sum of all the excesses. -/
theorem norm_le_one_add_trace_sub_one {A : Matrix n n ℝ} (hA : A.PosDef) (h : 1 ≤ A) :
    ‖A‖ ≤ 1 + Matrix.trace (A - 1) := by
  have hexc : ∀ i, (0 : ℝ) ≤ hA.isHermitian.eigenvalues i - 1 := fun i =>
    sub_nonneg.mpr
      (HCPolySupport.HighContrast.one_le_eigenvalues_of_one_le hA.isHermitian h i)
  have htr : Matrix.trace (A - 1) = ∑ i, (hA.isHermitian.eigenvalues i - 1) := by
    have hsum : A.trace = ∑ i, hA.isHermitian.eigenvalues i := by
      simpa using hA.isHermitian.trace_eq_sum_eigenvalues
    rw [Matrix.trace_sub, Matrix.trace_one, hsum, Finset.sum_sub_distrib]
    simp
  have hnn : (0 : ℝ) ≤ Matrix.trace (A - 1) := trace_sub_one_nonneg h
  refine norm_le_of_le_smul_one hA.posSemidef (by linarith only [hnn]) ?_
  refine HCPolySupport.HighContrast.le_smul_one_of_eigenvalues_le
    hA.isHermitian fun i => ?_
  have hle : hA.isHermitian.eigenvalues i - 1 ≤ ∑ j, (hA.isHermitian.eigenvalues j - 1) :=
    Finset.single_le_sum (f := fun j => hA.isHermitian.eigenvalues j - 1)
      (fun j _ => hexc j) (Finset.mem_univ i)
  rw [htr]
  linarith only [hle]

/-! ## Positivity and monotonicity of the trace of a product -/

/-- **The trace of a product of two positive semidefinite matrices is
nonnegative.**  Cyclicity turns `tr(XB)` into the trace of the congruence
`X^{1/2}BX^{1/2}`. -/
theorem trace_mul_nonneg {X B : Matrix n n ℝ} (hX : X.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (X * B) := by
  obtain ⟨hroot, hsq⟩ := matSqrt_spec hX
  have hcong : (matSqrt X * B * matSqrt X).PosSemidef := by
    have h0 := hB.conjTranspose_mul_mul_same (matSqrt X)
    rwa [hroot.isHermitian.eq] at h0
  have heq : Matrix.trace (X * B) = Matrix.trace (matSqrt X * B * matSqrt X) := by
    conv_lhs => rw [← hsq, Matrix.mul_assoc,
      Matrix.trace_mul_comm (matSqrt X) (matSqrt X * B)]
  rw [heq]
  exact hcong.trace_nonneg

/-- **The trace against a positive semidefinite matrix is monotone.** -/
theorem trace_mul_le_trace_mul {X M N : Matrix n n ℝ} (hX : X.PosSemidef) (h : M ≤ N) :
    Matrix.trace (X * M) ≤ Matrix.trace (X * N) := by
  have hPS : ((N : Matrix n n ℝ) - M).PosSemidef := Matrix.le_iff.mp h
  have hnn := trace_mul_nonneg hX hPS
  rw [Matrix.mul_sub, Matrix.trace_sub] at hnn
  linarith only [hnn]

/-- **The trace against a positive semidefinite matrix is bounded by its
spectral size.** -/
theorem trace_mul_le_norm_mul_trace {X M : Matrix n n ℝ} (hX : X.PosSemidef)
    (hM : M.PosSemidef) : Matrix.trace (X * M) ≤ ‖M‖ * Matrix.trace X := by
  have hstep := trace_mul_le_trace_mul hX (le_norm_smul_one hM)
  rwa [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at hstep

/-! ## The congruence step -/

/-- The spectral size of `CC^t` equals the spectral size of `C^tC`: both are the
square of the spectral size of `C`. -/
theorem norm_mul_transpose_eq (C : Matrix n n ℝ) : ‖C * Cᵀ‖ = ‖Cᵀ * C‖ := by
  have hone : ‖(Cᵀ)ᴴ * Cᵀ‖ = ‖Cᵀ‖ * ‖Cᵀ‖ := Matrix.l2_opNorm_conjTranspose_mul_self Cᵀ
  have htwo : ‖Cᴴ * C‖ = ‖C‖ * ‖C‖ := Matrix.l2_opNorm_conjTranspose_mul_self C
  have hthree : ‖Cᴴ‖ = ‖C‖ := Matrix.l2_opNorm_conjTranspose C
  rw [conjTranspose_eq_transpose' C] at htwo hthree
  rw [conjTranspose_eq_transpose' Cᵀ, Matrix.transpose_transpose] at hone
  rw [hone, htwo, hthree]

/-- **The congruence step of `p.fixed.geometry.one.grid.propagation`.**  If the congruence
`C^tC` is bounded by `c` in the Loewner order, then conjugating a positive
semidefinite matrix by `C` multiplies its trace by at most `c`. -/
theorem trace_conj_le {X C : Matrix n n ℝ} (hX : X.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : Cᵀ * C ≤ c • (1 : Matrix n n ℝ)) :
    Matrix.trace (Cᵀ * X * C) ≤ c * Matrix.trace X := by
  have hCC : (C * Cᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose C
    rwa [conjTranspose_eq_transpose' C] at this
  have hCtC : (Cᵀ * C).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self C
    rwa [conjTranspose_eq_transpose' C] at this
  have hnorm : ‖C * Cᵀ‖ ≤ c := by
    rw [norm_mul_transpose_eq C]
    exact norm_le_of_le_smul_one hCtC hc h
  have hcyc : Matrix.trace (Cᵀ * X * C) = Matrix.trace (X * (C * Cᵀ)) := by
    conv_lhs => rw [Matrix.trace_mul_comm (Cᵀ * X) C, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (C * Cᵀ) X]
  have hbound := trace_mul_le_norm_mul_trace hX hCC
  have htr : 0 ≤ Matrix.trace X := hX.trace_nonneg
  rw [hcyc]
  calc Matrix.trace (X * (C * Cᵀ)) ≤ ‖C * Cᵀ‖ * Matrix.trace X := hbound
    _ ≤ c * Matrix.trace X := mul_le_mul_of_nonneg_right hnorm htr

/-! ## The change of terminal normalization -/

/-- **The trace step of `p.fixed.geometry.one.grid.propagation`.**  For an ordered triple
`E_t ≤ E_s ≤ E_j` of positive definite matrices, the relative mean of `E_j` over
`E_t` is the congruence of the relative mean of `E_j` over `E_s` by
`R = E_s^{1/2}E_t^{-1/2}`, whose own congruence `R^tR` is the relative mean of
`E_s` over `E_t`; cyclicity and positivity of the trace then give the printed
bound on the trace gap. -/
theorem one_add_trace_normalize_le {Ej Es Et : Matrix n n ℝ}
    (hEs : Es.PosDef) (hEt : Et.PosDef) (hsj : Es ≤ Ej) (hts : Et ≤ Es) :
    1 + Matrix.trace (matSqrt Et⁻¹ * Ej * matSqrt Et⁻¹ - 1) ≤
      (1 + Matrix.trace (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ - 1)) *
        (1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1)) := by
  have hEssq : matSqrt Es * matSqrt Es = Es := (matSqrt_spec hEs.posSemidef).2
  have hEssymm : (matSqrt Es)ᵀ = matSqrt Es :=
    isSymm_of_isHermitian (matSqrt_spec hEs.posSemidef).1.isHermitian
  have hEtsymm : (matSqrt Et⁻¹)ᵀ = matSqrt Et⁻¹ := transpose_matSqrt_inv hEt
  have hCt : (matSqrt Es * matSqrt Et⁻¹)ᵀ = matSqrt Et⁻¹ * matSqrt Es := by
    rw [Matrix.transpose_mul, hEssymm, hEtsymm]
  have hCtC : (matSqrt Es * matSqrt Et⁻¹)ᵀ * (matSqrt Es * matSqrt Et⁻¹) =
      matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ := by
    rw [hCt, Matrix.mul_assoc, ← Matrix.mul_assoc (matSqrt Es) (matSqrt Es), hEssq,
      ← Matrix.mul_assoc]
  have hcongr := Recurrence.normalize_congr (Ej := Es) (Ep := Et) (X := Ej) hEs hEt
  have hone_js : (1 : Matrix n n ℝ) ≤ matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ :=
    Recurrence.one_le_normalize hEs hsj
  have hone_st : (1 : Matrix n n ℝ) ≤ matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ :=
    Recurrence.one_le_normalize hEt hts
  have hPst : (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹).PosDef := posDef_normalize hEs hEt
  have hy0 : 0 ≤ Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1) :=
    trace_sub_one_nonneg hone_st
  have hXPS : ((matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ : Matrix n n ℝ) - 1).PosSemidef :=
    Matrix.le_iff.mp hone_js
  have hnormst : ‖matSqrt Et⁻¹ * Es * matSqrt Et⁻¹‖ ≤
      1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1) :=
    norm_le_one_add_trace_sub_one hPst hone_st
  have hbound : (matSqrt Es * matSqrt Et⁻¹)ᵀ * (matSqrt Es * matSqrt Et⁻¹) ≤
      (1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1)) • (1 : Matrix n n ℝ) := by
    rw [hCtC]
    exact le_smul_one_of_norm_le hPst.posSemidef hnormst
  have hconj := trace_conj_le hXPS
    (c := 1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1))
    (by linarith only [hy0]) hbound
  have hsplit : (matSqrt Es * matSqrt Et⁻¹)ᵀ * (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹) *
      (matSqrt Es * matSqrt Et⁻¹) =
      (matSqrt Es * matSqrt Et⁻¹)ᵀ * (matSqrt Es * matSqrt Et⁻¹) +
        (matSqrt Es * matSqrt Et⁻¹)ᵀ * (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ - 1) *
          (matSqrt Es * matSqrt Et⁻¹) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  have htrace : Matrix.trace (matSqrt Et⁻¹ * Ej * matSqrt Et⁻¹) =
      Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹) +
        Matrix.trace ((matSqrt Es * matSqrt Et⁻¹)ᵀ *
          (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ - 1) * (matSqrt Es * matSqrt Et⁻¹)) := by
    rw [hcongr, hsplit, Matrix.trace_add, hCtC]
  have hA : Matrix.trace (matSqrt Et⁻¹ * Ej * matSqrt Et⁻¹ - 1)
      = Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1) +
        Matrix.trace ((matSqrt Es * matSqrt Et⁻¹)ᵀ * (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ - 1) *
          (matSqrt Es * matSqrt Et⁻¹)) := by
    rw [Matrix.trace_sub, htrace, Matrix.trace_sub]
    ring
  have hexpand : (1 + Matrix.trace (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ - 1)) *
      (1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1))
      = 1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1) +
        (1 + Matrix.trace (matSqrt Et⁻¹ * Es * matSqrt Et⁻¹ - 1)) *
          Matrix.trace (matSqrt Es⁻¹ * Ej * matSqrt Es⁻¹ - 1) := by
    ring
  rw [hA, hexpand]
  linarith only [hconj]

end

end PortableHistory
end HighContrast
end HCPolySupport
