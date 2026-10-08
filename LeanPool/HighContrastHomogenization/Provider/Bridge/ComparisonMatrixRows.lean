/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowMomentBound
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution
public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportCoefficients
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.CheckpointMoment
public import LeanPool.HighContrastHomogenization.Provider.ShortHop.Eccentricity
public import LeanPool.HighContrastHomogenization.Provider.Transport.TransportMeanDomination
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSup
public import LeanPool.HighContrastHomogenization.Provider.Transport.AnnealedRows
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSpectral

/-!
# High-contrast homogenization: Provider.Bridge.ComparisonMatrixRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Matrix rows for two-grid comparison

Each positive increment is measured by its trace in the terminal geometry.
The scalar boundary-row estimate then lifts directly to a Loewner estimate for
the corresponding weighted row of adapted means.
-/

namespace HCPolySupport
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem sum_Icc_sub_pred {M : Type*} [AddCommGroup M] (f : ℤ → M)
    {u v : ℤ} (huv : u ≤ v) :
    ∑ j ∈ Finset.Icc (u + 1) v, (f (j - 1) - f j) = f u - f v := by
  induction v, huv using Int.leInduction with
  | base =>
    have hempty : Finset.Icc (u + 1) u = (∅ : Finset ℤ) := by
      ext x
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and, not_le]
      omega
    rw [hempty, Finset.sum_empty, sub_self]
  | succ w hw ih =>
    have hins : Finset.Icc (u + 1) (w + 1) =
        insert (w + 1) (Finset.Icc (u + 1) w) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (w + 1) ∉ Finset.Icc (u + 1) w := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [hins, Finset.sum_insert hnot, ih, add_sub_cancel_right]
    abel

/-- A positive semidefinite matrix is bounded by its trace in any positive
terminal geometry. -/
theorem posSemidef_le_trace_inv_smul {A G : FullBlockMat d}
    (hA : A.PosDef) (hG : G.PosSemidef) :
    G ≤ Matrix.trace (A⁻¹ * G) • A := by
  let S : FullBlockMat d := matSqrt A⁻¹
  have hnorm : (S * G * S).PosSemidef := posSemidef_normalize hG hA
  have htrace : Matrix.trace (S * G * S) = Matrix.trace (A⁻¹ * G) := by
    calc
      Matrix.trace (S * G * S) = Matrix.trace (S * (S * G)) :=
        Matrix.trace_mul_comm (S * G) S
      _ = Matrix.trace ((S * S) * G) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (A⁻¹ * G) := by rw [matSqrt_inv_mul_self hA]
  have hle := Recurrence.le_trace_smul_one hnorm
  rw [htrace] at hle
  exact (conj_normalize hA (Matrix.trace (A⁻¹ * G))).mpr hle

/-- An earlier positive mean is bounded by the terminal mean and the trace of
their positive difference in the terminal geometry. -/
theorem matrix_le_terminal_trace_sub {A B : FullBlockMat d}
    (hB : B.PosDef) (hBA : B ≤ A) :
    A ≤ (1 + Matrix.trace (B⁻¹ * (A - B))) • B := by
  have hG : (A - B).PosSemidef := Matrix.le_iff.mp hBA
  have htrace := posSemidef_le_trace_inv_smul hB hG
  refine Matrix.le_iff.mpr ?_
  have hps := Matrix.le_iff.mp htrace
  rw [add_smul, one_smul]
  have heq : B + Matrix.trace (B⁻¹ * (A - B)) • B - A =
      Matrix.trace (B⁻¹ * (A - B)) • B - (A - B) := by abel
  rw [heq]
  exact hps

end

end Bridge
end HighContrast
end HCPolySupport
