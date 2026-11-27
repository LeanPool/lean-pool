/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FiniteRenyiThreeLines

/-!
# The actual normalized positive Hilbert--Schmidt dual matrix

For a strictly positive matrix in nonzero finite dimension, the positive
matrix divided by sqrt(Tr(A^2)) is the genuine Hilbert--Schmidt norm-one
dual test. The trace pairing equals sqrt(Tr(A^2)). Empty matrices will be
handled separately at the finite interpolation endpoint.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem hilbertSchmidt_rpow_two (A : Matrix ι ι ℂ) (hA : 0 ≤ A) :
    A ^ (2 : ℝ) = A * A := by
  simpa only [Nat.cast_ofNat, pow_two] using CFC.rpow_natCast A 2 hA

/-- Finite Hilbert schmidt dual given by `(Real.sqrt ((A ^ (2 : ℝ)).trace.re))⁻¹ • A`. -/
def finiteHilbertSchmidtDual (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Real.sqrt ((A ^ (2 : ℝ)).trace.re))⁻¹ • A

theorem real_trace_positive_square_pos [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    0 < (A ^ (2 : ℝ)).trace.re := by
  rw [complex_trace_positive_rpow hA 2, Complex.ofReal_re]
  let i : ι := Classical.arbitrary ι
  exact (Real.rpow_pos_of_pos (hA.eigenvalues_pos i) 2).trans_le
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Real.rpow_nonneg (hA.eigenvalues_pos j).le 2) (Finset.mem_univ i))

theorem finiteHilbertSchmidtDual_posDef [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    (finiteHilbertSchmidtDual A).PosDef :=
  hA.smul (inv_pos.mpr (Real.sqrt_pos.mpr (real_trace_positive_square_pos hA)))

theorem finiteHilbertSchmidtDual_square_trace [Nonempty ι] {A : Matrix ι ι ℂ}
    (hA : A.PosDef) : ((finiteHilbertSchmidtDual A) ^ (2 : ℝ)).trace.re = 1 := by
  let N := (A ^ (2 : ℝ)).trace.re
  let c := (Real.sqrt N)⁻¹
  have hN : 0 < N := real_trace_positive_square_pos hA
  have hNs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hX := finiteHilbertSchmidtDual_posDef hA
  have hn : (A * A).trace.re = N := by
    dsimp only [N]
    rw [hilbertSchmidt_rpow_two A hA.posSemidef.nonneg]
  have hc : c * c * N = 1 := by
    dsimp only [c]
    field_simp [hNs]
    nlinarith [Real.sq_sqrt hN.le]
  rw [hilbertSchmidt_rpow_two _ hX.posSemidef.nonneg]
  change ((c • A) * (c • A)).trace.re = 1
  rw [smul_mul_smul_comm, Matrix.trace_smul, ← RCLike.re_eq_complex_re,
    RCLike.smul_re, RCLike.re_eq_complex_re, hn]
  exact hc

theorem norm_trace_finiteHilbertSchmidtDual_mul [Nonempty ι] {A : Matrix ι ι ℂ}
    (hA : A.PosDef) : ‖(finiteHilbertSchmidtDual A * A).trace‖ =
      Real.sqrt ((A ^ (2 : ℝ)).trace.re) := by
  let N := (A ^ (2 : ℝ)).trace.re
  let c := (Real.sqrt N)⁻¹
  have hN : 0 < N := real_trace_positive_square_pos hA
  have hNs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hN)
  have ht : (A * A).trace = (N : ℂ) := by
    have h := complex_trace_positive_rpow hA 2
    have hr := congrArg Complex.re h
    rw [Complex.ofReal_re] at hr
    rw [hilbertSchmidt_rpow_two A hA.posSemidef.nonneg] at h
    exact h.trans (congrArg (fun x : ℝ => (x : ℂ)) hr.symm)
  change ‖((c • A) * A).trace‖ = Real.sqrt N
  rw [smul_mul_assoc, Matrix.trace_smul, ht, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN]
  dsimp only [c]
  apply (mul_left_cancel₀ hNs)
  rw [← mul_assoc, mul_inv_cancel₀ hNs, one_mul]
  nlinarith [Real.sq_sqrt hN.le]

end VacuumBellSeparation.Gaussian
