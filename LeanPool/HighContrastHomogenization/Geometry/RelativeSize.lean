/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder

/-!
# High-contrast homogenization: Geometry.RelativeSize

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The relative size of one positive matrix against another

The generalized eigenvalue functional `Λ(F;E) = |F^{-1/2} E F^{-1/2}|` of the
reference text — it appears as the reference imbalance `κ_ref` of the entry
comparison, and as the imbalance `𝔡` of `e.response.canonical.imbalance` — is
written here as

    relSize E F = ‖matSqrt F⁻¹ * E * matSqrt F⁻¹‖,

so that the numerator is the first argument and the denominator the second.

The whole file rests on one observation: conjugation by `F^{-1/2}` is a
congruence that sends `F` to the identity, so a Loewner comparison `E ≤ t F`
becomes a comparison against `t I`, which the spectral norm reads off exactly.
The resulting characterization

    relSize E F ≤ t ↔ E ≤ t • F        (`relSize_le_iff`, for `0 ≤ t`)

says that `relSize E F` is the *least* scalar `t` with `E ≤ t F`.  Every other
statement below is a formal consequence of it, including the invariance under a
common congruence

    relSize (Cᴴ E C) (Cᴴ F C) = relSize E F   (`relSize_congr`),

which is the "generalized eigenvalues are unchanged under a common congruence"
step of the canonical balance.

The relative size of a positive definite matrix against itself is `‖1‖`, which
is `1` exactly when the index type is nonempty; the few statements that need
that normalization carry a `Nonempty` instance.
-/

namespace HCPolySupport
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Scalar dilations and the Loewner order -/

omit [Fintype n] [DecidableEq n] in
/-- Dilation by a nonnegative scalar is monotone for the Loewner order. -/
theorem smul_le_smul_of_le {A B : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c) (h : A ≤ B) :
    c • A ≤ c • B := by
  refine Matrix.le_iff.mpr ?_
  have hrw : c • B - c • A = c • (B - A) := (smul_sub c B A).symm
  rw [hrw]
  exact (Matrix.le_iff.mp h).smul hc

/-- Congruence by an invertible matrix preserves positive definiteness. -/
theorem posDef_conj {Q C : Matrix n n ℝ} (hQ : Q.PosDef) (hC : IsUnit C) :
    (Cᴴ * Q * C).PosDef :=
  hQ.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hC)

/-! ## Normalization by the inverse square root -/

/-- The inverse square root of a positive definite `Q` is symmetric. -/
theorem conjTranspose_matSqrt_inv {Q : Matrix n n ℝ} (hQ : Q.PosDef) :
    (matSqrt Q⁻¹)ᴴ = matSqrt Q⁻¹ :=
  (matSqrt_spec hQ.inv.posSemidef).1.isHermitian

/-- The inverse square root of a positive definite matrix is invertible. -/
theorem isUnit_matSqrt_inv {Q : Matrix n n ℝ} (hQ : Q.PosDef) : IsUnit (matSqrt Q⁻¹) :=
  isUnit_matSqrt hQ.inv

/-- **Normalization.**  Conjugating by `Q^{-1/2}` turns a scalar Loewner bound
against `Q` into a scalar Loewner bound against the identity, because the
conjugation sends `Q` to `1`. -/
theorem conj_normalize {P Q : Matrix n n ℝ} (hQ : Q.PosDef) (t : ℝ) :
    P ≤ t • Q ↔ matSqrt Q⁻¹ * P * matSqrt Q⁻¹ ≤ t • (1 : Matrix n n ℝ) := by
  have hsymm : (matSqrt Q⁻¹)ᴴ = matSqrt Q⁻¹ := conjTranspose_matSqrt_inv hQ
  have key := conj_le_conj_iff (A := P) (B := t • Q) (isUnit_matSqrt_inv hQ)
  rw [hsymm] at key
  have hrhs : matSqrt Q⁻¹ * (t • Q) * matSqrt Q⁻¹ = t • (1 : Matrix n n ℝ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, matSqrt_inv_conj hQ]
  rw [hrhs] at key
  exact key.symm

/-- Normalization preserves positive semidefiniteness. -/
theorem posSemidef_normalize {P Q : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosDef) :
    (matSqrt Q⁻¹ * P * matSqrt Q⁻¹).PosSemidef := by
  have h := hP.conjTranspose_mul_mul_same (B := matSqrt Q⁻¹)
  rwa [conjTranspose_matSqrt_inv hQ] at h

/-- Normalization preserves positive definiteness. -/
theorem posDef_normalize {P Q : Matrix n n ℝ} (hP : P.PosDef) (hQ : Q.PosDef) :
    (matSqrt Q⁻¹ * P * matSqrt Q⁻¹).PosDef := by
  have h := posDef_conj hP (isUnit_matSqrt_inv hQ)
  rwa [conjTranspose_matSqrt_inv hQ] at h

/-! ## The relative size -/

/-- The relative size `Λ(Q;P) = |Q^{-1/2} P Q^{-1/2}|` of `P` against `Q`: the
scalar size of `P` measured in the geometry of `Q`. -/
@[expose]
def relSize (P Q : Matrix n n ℝ) : ℝ := ‖matSqrt Q⁻¹ * P * matSqrt Q⁻¹‖

theorem relSize_def (P Q : Matrix n n ℝ) :
    relSize P Q = ‖matSqrt Q⁻¹ * P * matSqrt Q⁻¹‖ := rfl

theorem relSize_nonneg (P Q : Matrix n n ℝ) : 0 ≤ relSize P Q := norm_nonneg _

/-- **The relative size is the least scalar Loewner bound.**  This is the only
property of `relSize` used downstream; everything below is a consequence. -/
theorem relSize_le_iff {P Q : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosDef) {t : ℝ}
    (ht : 0 ≤ t) : relSize P Q ≤ t ↔ P ≤ t • Q := by
  rw [relSize_def, norm_le_iff_le_smul_one (posSemidef_normalize hP hQ) ht]
  exact (conj_normalize hQ t).symm

/-- The relative size realizes its own bound. -/
theorem le_relSize_smul {P Q : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosDef) :
    P ≤ relSize P Q • Q :=
  (relSize_le_iff hP hQ (relSize_nonneg P Q)).mp le_rfl

/-- The relative size of a positive definite matrix against itself is `‖1‖`. -/
theorem relSize_self {Q : Matrix n n ℝ} (hQ : Q.PosDef) :
    relSize Q Q = ‖(1 : Matrix n n ℝ)‖ := by
  rw [relSize_def, matSqrt_inv_conj hQ]

/-- On a nonempty index type the relative size of a positive definite matrix
against itself is one. -/
theorem relSize_self_eq_one [Nonempty n] {Q : Matrix n n ℝ} (hQ : Q.PosDef) :
    relSize Q Q = 1 := by rw [relSize_self hQ, norm_one]

/-- The relative size is monotone in the numerator. -/
theorem relSize_mono_left {P₁ P₂ Q : Matrix n n ℝ} (hP₁ : P₁.PosSemidef)
    (hP₂ : P₂.PosSemidef) (hQ : Q.PosDef) (h : P₁ ≤ P₂) :
    relSize P₁ Q ≤ relSize P₂ Q :=
  (relSize_le_iff hP₁ hQ (relSize_nonneg P₂ Q)).mpr (h.trans (le_relSize_smul hP₂ hQ))

/-- The relative size is antitone in the denominator. -/
theorem relSize_anti_right {P Q₁ Q₂ : Matrix n n ℝ} (hP : P.PosSemidef) (hQ₁ : Q₁.PosDef)
    (hQ₂ : Q₂.PosDef) (h : Q₁ ≤ Q₂) : relSize P Q₂ ≤ relSize P Q₁ :=
  (relSize_le_iff hP hQ₂ (relSize_nonneg P Q₁)).mpr
    ((le_relSize_smul hP hQ₁).trans (smul_le_smul_of_le (relSize_nonneg P Q₁) h))

/-- The relative size is homogeneous of degree one in the numerator. -/
theorem relSize_smul_left {c : ℝ} (hc : 0 ≤ c) (P Q : Matrix n n ℝ) :
    relSize (c • P) Q = c * relSize P Q := by
  simp only [relSize_def]
  rw [Matrix.mul_smul, Matrix.smul_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

/-- The relative size is homogeneous of degree minus one in the denominator. -/
theorem relSize_smul_right {c : ℝ} (hc : 0 < c) {P Q : Matrix n n ℝ} (hP : P.PosSemidef)
    (hQ : Q.PosDef) : relSize P (c • Q) = c⁻¹ * relSize P Q := by
  have hcQ : (c • Q).PosDef := hQ.smul hc
  have hcinv : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  refine le_antisymm ?_ ?_
  · refine (relSize_le_iff hP hcQ (mul_nonneg hcinv (relSize_nonneg P Q))).mpr ?_
    have hrw : (c⁻¹ * relSize P Q) • (c • Q) = relSize P Q • Q := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [hrw]
    exact le_relSize_smul hP hQ
  · have h1 : relSize P Q ≤ c * relSize P (c • Q) := by
      refine (relSize_le_iff hP hQ (mul_nonneg hc.le (relSize_nonneg P (c • Q)))).mpr ?_
      have h2 := le_relSize_smul hP hcQ
      rwa [smul_smul, mul_comm (relSize P (c • Q)) c] at h2
    have h3 : c⁻¹ * relSize P Q ≤ c⁻¹ * (c * relSize P (c • Q)) :=
      mul_le_mul_of_nonneg_left h1 hcinv
    rwa [inv_mul_cancel_left₀ hc.ne'] at h3

/-- **Invariance under a common congruence.**  Generalized eigenvalues do not
see an invertible change of coordinates; this is the step the canonical balance
takes when it moves the imbalance between `E` and its normalized form. -/
theorem relSize_congr {P Q C : Matrix n n ℝ} (hP : P.PosSemidef) (hQ : Q.PosDef)
    (hC : IsUnit C) : relSize (Cᴴ * P * C) (Cᴴ * Q * C) = relSize P Q := by
  have hPC : (Cᴴ * P * C).PosSemidef := hP.conjTranspose_mul_mul_same (B := C)
  have hQC : (Cᴴ * Q * C).PosDef := posDef_conj hQ hC
  refine le_antisymm ?_ ?_
  · refine (relSize_le_iff hPC hQC (relSize_nonneg P Q)).mpr ?_
    have h := conj_le_conj C (le_relSize_smul hP hQ)
    rwa [Matrix.mul_smul, Matrix.smul_mul] at h
  · refine (relSize_le_iff hP hQ (relSize_nonneg (Cᴴ * P * C) (Cᴴ * Q * C))).mpr ?_
    have h := le_relSize_smul hPC hQC
    rw [← Matrix.smul_mul, ← Matrix.mul_smul] at h
    exact (conj_le_conj_iff hC).mp h

/-- Measuring the identity against a positive definite `X` reads off the size of
`X⁻¹`. -/
theorem relSize_one_left {X : Matrix n n ℝ} (hX : X.PosDef) : relSize 1 X = ‖X⁻¹‖ := by
  rw [relSize_def, Matrix.mul_one, (matSqrt_spec hX.inv.posSemidef).2]

/-- **The reciprocal reading of the relative size.**  With
`X := m₀^{-1/2} m₁ m₀^{-1/2}`, the relative size of `m₀` against `m₁` is the
size of `X⁻¹`, while the relative size of `m₁` against `m₀` is the size of `X`
by definition.  Since `X` is positive definite, `‖X‖` is its largest eigenvalue
and `‖X⁻¹‖` the reciprocal of its smallest. -/
theorem relSize_eq_norm_normalize_inv {m₀ m₁ : Matrix n n ℝ} (h₀ : m₀.PosDef)
    (h₁ : m₁.PosDef) :
    relSize m₀ m₁ = ‖(matSqrt m₀⁻¹ * m₁ * matSqrt m₀⁻¹)⁻¹‖ := by
  have hcong := relSize_congr h₀.posSemidef h₁ (isUnit_matSqrt_inv h₀)
  rw [conjTranspose_matSqrt_inv h₀, matSqrt_inv_conj h₀] at hcong
  rw [← hcong, relSize_one_left (posDef_normalize h₁ h₀)]

/-! ## Two-sided comparison -/

/-- **The two relative sizes of a pair multiply to at least one.**  The product
is the ratio of the largest to the smallest generalized eigenvalue. -/
theorem one_le_relSize_mul_relSize [Nonempty n] {P Q : Matrix n n ℝ} (hP : P.PosDef)
    (hQ : Q.PosDef) : 1 ≤ relSize P Q * relSize Q P := by
  have h1 : P ≤ relSize P Q • Q := le_relSize_smul hP.posSemidef hQ
  have h2 : relSize P Q • Q ≤ relSize P Q • (relSize Q P • P) :=
    smul_le_smul_of_le (relSize_nonneg P Q) (le_relSize_smul hQ.posSemidef hP)
  have h3 : P ≤ (relSize P Q * relSize Q P) • P := by
    rw [← smul_smul]
    exact h1.trans h2
  have h4 : relSize P P ≤ relSize P Q * relSize Q P :=
    (relSize_le_iff hP.posSemidef hP
      (mul_nonneg (relSize_nonneg P Q) (relSize_nonneg Q P))).mpr h3
  rwa [relSize_self_eq_one hP] at h4

/-- The relative size of a pair of positive definite matrices is positive. -/
theorem relSize_pos [Nonempty n] {P Q : Matrix n n ℝ} (hP : P.PosDef) (hQ : Q.PosDef) :
    0 < relSize P Q := by
  rcases lt_or_eq_of_le (relSize_nonneg P Q) with h | h
  · exact h
  · exfalso
    have hkey := one_le_relSize_mul_relSize hP hQ
    rw [← h, zero_mul] at hkey
    linarith only [hkey]

end

end HighContrast
end HCPolySupport
