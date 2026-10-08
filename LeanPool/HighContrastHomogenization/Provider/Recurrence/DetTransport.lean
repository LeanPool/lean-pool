/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.DetOrder

/-!
# High-contrast homogenization: Provider.Recurrence.DetTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Determinant transport for the fixed-grid recurrence

The proof of `p.fixed.geometry.parent.child.recurrence` compares two consecutive adapted
scales through the relative mean `P = E_p^{-1/2} E_j E_p^{-1/2}`.  Once the mean
order `E_p ≤ E_j` is available, everything the recurrence asks of `P` is a
statement about a positive definite matrix above the identity, and that is what
is proved here.

The determinant identities for the parent-child normalization read
`det P = e^{Δ}`, `Δ ≥ 0` and `|P| ≤ e^{Δ}` for the determinant increment
`Δ = log det E_j - log det E_p`.  The determinant identity is the change of
variables under the congruence; the sign of `Δ` is monotonicity of the
determinant for the Loewner order; and the spectral bound is the observation
that the largest eigenvalue of a matrix above the identity is at most the
product of all of them.

The recurrence then needs the trace gap `b = tr(P - I)`, and the step
`b = Σ(λ_i - 1) ≤ Π λ_i - 1 = e^{Δ} - 1` of the fixed-grid proof.  Its content
is the elementary inequality that for reals at least one the sum of the excesses
is at most the excess of the product, proved here by induction on the index set
and then read on the eigenvalues.

Finally the fixed-grid proof passes from the child normalization to the parent
one by "the exact congruence"
`E_p^{-1/2}(G - E_j)E_p^{-1/2} = C^t (E_j^{-1/2}(G - E_j)E_j^{-1/2}) C` with
`C = E_j^{1/2} E_p^{-1/2}`.  That identity holds for an arbitrary matrix in
place of `G` and is pure square-root algebra; it is recorded in that generality.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The sum of excesses and the excess of the product -/

/-- For reals at least one, the sum of the excesses over one is at most the
excess over one of the product.  Adjoining a factor multiplies the product by
`f a` and adds `f a - 1` to the sum, and the two differ by the nonnegative
product `(f a - 1)(∏ f - 1)`. -/
theorem sum_sub_one_le_prod_sub_one {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 1 ≤ f i) : ∑ i ∈ s, (f i - 1) ≤ (∏ i ∈ s, f i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hfa : 1 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, 1 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hprod : (1 : ℝ) ≤ ∏ i ∈ s, f i := by
        have hbound := Finset.prod_le_prod₀ (s := s) (f := fun _ => (1 : ℝ)) (g := f)
          (fun _ _ => zero_le_one) fun i hi => hrest i hi
        simpa using hbound
      have hstep := ih hrest
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      nlinarith only [hfa, hprod, hstep]

/-! ## The trace gap -/

/-- **The trace gap of a matrix above the identity is at most its determinant
gap.**  This is the step `b = Σ(λ_i - 1) ≤ Π λ_i - 1` of the fixed-grid
recurrence, read on the eigenvalues of the relative mean. -/
theorem trace_sub_one_le_det_sub_one {A : Matrix n n ℝ} (hA : A.IsHermitian) (h : 1 ≤ A) :
    Matrix.trace (A - 1) ≤ A.det - 1 := by
  have hsum : A.trace = ∑ i, hA.eigenvalues i := by
    simpa using hA.trace_eq_sum_eigenvalues
  have hdet : A.det = ∏ i, hA.eigenvalues i := by
    simpa using hA.det_eq_prod_eigenvalues
  have hkey := sum_sub_one_le_prod_sub_one (Finset.univ : Finset n) hA.eigenvalues
    fun i _ => HCPolySupport.HighContrast.one_le_eigenvalues_of_one_le hA h i
  rw [Finset.sum_sub_distrib] at hkey
  rw [Matrix.trace_sub, Matrix.trace_one, hsum, hdet]
  simpa using hkey

/-! ## The determinant transport display -/

/-- The determinant increment is the logarithm of the determinant of the
relative mean. -/
theorem det_normalize_eq_exp {Ej Ep : Matrix n n ℝ} (hEj : Ej.PosDef) (hEp : Ep.PosDef) :
    (matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹).det
      = Real.exp (Real.log Ej.det - Real.log Ep.det) := by
  rw [det_conj_matSqrt_inv hEp, Real.exp_sub, Real.exp_log hEj.det_pos,
    Real.exp_log hEp.det_pos]

/-- The relative mean of an ordered pair of positive definite matrices lies
above the identity: this is the mean order `E_p ≤ E_j` conjugated by
`E_p^{-1/2}`. -/
theorem one_le_normalize {Ej Ep : Matrix n n ℝ} (hEp : Ep.PosDef) (h : Ep ≤ Ej) :
    (1 : Matrix n n ℝ) ≤ matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹ := by
  have hcong := conj_le_conj' (conjTranspose_matSqrt_inv hEp) h
  rwa [matSqrt_inv_conj hEp] at hcong

/-- **The determinant identities for the parent-child normalization of the
fixed-grid recurrence.**  For an ordered pair of positive definite means
the relative mean `P = E_p^{-1/2} E_j E_p^{-1/2}` lies above the identity, its
determinant is `e^{Δ}` for the determinant increment
`Δ = log det E_j - log det E_p`, that increment is nonnegative, the spectral
size of `P` is at most `e^{Δ}`, and the trace gap `tr(P - I)` is at most
`e^{Δ} - 1`. -/
theorem determinant_transport {Ej Ep : Matrix n n ℝ} (hEj : Ej.PosDef) (hEp : Ep.PosDef)
    (h : Ep ≤ Ej) :
    (1 : Matrix n n ℝ) ≤ matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹ ∧
      0 ≤ Real.log Ej.det - Real.log Ep.det ∧
      (matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹).det
          = Real.exp (Real.log Ej.det - Real.log Ep.det) ∧
        ‖matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹‖
            ≤ Real.exp (Real.log Ej.det - Real.log Ep.det) ∧
          Matrix.trace (matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹ - 1)
            ≤ Real.exp (Real.log Ej.det - Real.log Ep.det) - 1 := by
  have hone : (1 : Matrix n n ℝ) ≤ matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹ := one_le_normalize hEp h
  have hPpos : (matSqrt Ep⁻¹ * Ej * matSqrt Ep⁻¹).PosDef := posDef_normalize hEj hEp
  have hdet := det_normalize_eq_exp hEj hEp
  have hincr : 0 ≤ Real.log Ej.det - Real.log Ep.det := by
    have hmono : Ep.det ≤ Ej.det := det_le_det_of_le hEp hEj h
    have := Real.log_le_log hEp.det_pos hmono
    linarith only [this]
  refine ⟨hone, hincr, hdet, ?_, ?_⟩
  · have hnorm := norm_le_det_of_one_le hPpos hone
    rwa [hdet] at hnorm
  · have htr := trace_sub_one_le_det_sub_one hPpos.isHermitian hone
    rwa [hdet] at htr

/-! ## The congruence between the two normalizations -/

/-- The square root of a positive definite matrix and the square root of its
inverse are mutually inverse. -/
private theorem matSqrt_mul_matSqrt_inv {A : Matrix n n ℝ} (hA : A.PosDef) :
    matSqrt A * matSqrt A⁻¹ = 1 := by
  rw [matSqrt_inv hA]
  exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (isUnit_matSqrt hA))

/-- The square root of the inverse and the square root are mutually inverse in
the other order as well. -/
private theorem matSqrt_inv_mul_matSqrt {A : Matrix n n ℝ} (hA : A.PosDef) :
    matSqrt A⁻¹ * matSqrt A = 1 := by
  rw [matSqrt_inv hA]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_iff_isUnit_det _ |>.mp (isUnit_matSqrt hA))

/-- **The exact congruence of the fixed-grid recurrence.**  Passing from the
child normalization by `E_j` to the parent normalization by `E_p` is conjugation
by `C = E_j^{1/2} E_p^{-1/2}`; the identity holds for an arbitrary matrix in the
centered slot, which is where the averaged child response enters. -/
theorem normalize_congr {Ej Ep X : Matrix n n ℝ} (hEj : Ej.PosDef) (hEp : Ep.PosDef) :
    matSqrt Ep⁻¹ * X * matSqrt Ep⁻¹ =
      (matSqrt Ej * matSqrt Ep⁻¹)ᵀ * (matSqrt Ej⁻¹ * X * matSqrt Ej⁻¹) *
        (matSqrt Ej * matSqrt Ep⁻¹) := by
  have hSsymm : (matSqrt Ep⁻¹)ᵀ = matSqrt Ep⁻¹ := transpose_matSqrt_inv hEp
  have hTsymm : (matSqrt Ej)ᵀ = matSqrt Ej :=
    isSymm_of_isHermitian (matSqrt_spec hEj.posSemidef).1.isHermitian
  rw [Matrix.transpose_mul, hSsymm, hTsymm]
  calc matSqrt Ep⁻¹ * X * matSqrt Ep⁻¹
      = matSqrt Ep⁻¹ * (1 * X * 1) * matSqrt Ep⁻¹ := by
        rw [Matrix.one_mul, Matrix.mul_one]
    _ = matSqrt Ep⁻¹ * ((matSqrt Ej * matSqrt Ej⁻¹) * X * (matSqrt Ej⁻¹ * matSqrt Ej)) *
          matSqrt Ep⁻¹ := by
        rw [matSqrt_mul_matSqrt_inv hEj, matSqrt_inv_mul_matSqrt hEj]
    _ = matSqrt Ep⁻¹ * matSqrt Ej * (matSqrt Ej⁻¹ * X * matSqrt Ej⁻¹) *
          (matSqrt Ej * matSqrt Ep⁻¹) := by
        simp only [Matrix.mul_assoc]

end

end Recurrence
end HighContrast
end HCPolySupport
