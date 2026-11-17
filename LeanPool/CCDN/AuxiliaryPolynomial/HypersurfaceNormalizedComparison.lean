/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
public import LeanPool.CCDN.Determinant.HypersurfaceHeightDeterminant
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceHeightComparison

/-! The normalized higher-dimensional determinant inequality, retaining the
exact root-rank and kernel-rank coefficients needed for uniform degree selection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Absorb the archimedean rank terms and divide by Ms. No fixed-factor
approximation of the leading rank or coefficient-height term is made. -/
theorem hypersurface_rank_comparison_normalized {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
    (B L A E : ℝ)
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) *
          (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((r + 1 + M).choose M : ℝ) +
        s * M * Real.log B - (((r + 1 + M).choose M : ℝ) - s) * Real.log L) :
    (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) / ((r + 1 : ℝ) * M) *
      (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) -
        (E + (r + 1 : ℝ) * hypersurfaceArchimedeanError r / (r.factorial : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) * Real.log L := by
  have hMs := hypersurface_rank_ge_degree_parameter hrpos hd hdM hr
  have hs0 : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hr1 : (r + 1 : ℝ) ≠ 0 := by positivity
  have hfac : (r.factorial : ℝ) ^ (1 / (r : ℝ)) ≠ 0 := by positivity
  have harch := hypersurface_rank_archimedean_error hrpos hd hdM hr
  have hkernel : ((r + 1 + M).choose M : ℝ) - s = (r + 1 + (M - d)).choose (M - d) := by
    have hh : (s : ℝ) + ((r + 1 + (M - d)).choose (M - d) : ℝ) = (r + 1 + M).choose M := by
      exact_mod_cast hr
    linarith
  rw [hkernel] at hcomparison
  let T := Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E
  let U := (r + 1 : ℝ) * hypersurfaceArchimedeanError r / (r.factorial : ℝ) ^ (1 / (r : ℝ))
  have hsplit : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (r : ℝ)) * (T - U) =
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) * T -
          hypersurfaceArchimedeanError r * (s : ℝ) ^ (1 + 1 / (r : ℝ)) := by
    dsimp only [U]
    field_simp
  have hraw : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (r : ℝ)) * (T - U) ≤
        s * M * Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) * Real.log L := by
    rw [hsplit]
    dsimp only [T]
    linarith
  have hquot := div_le_div_of_nonneg_right hraw (mul_nonneg hM0.le hs0.le)
  convert hquot using 1
  · rw [Real.rpow_add hs0, Real.rpow_one]
    dsimp only [T, U]
    field_simp
    ring
  · field_simp

/-- A dimension-only error for the normalized, height-controlled inequality. -/
def hypersurfaceNormalizedError (n : ℕ) : ℝ :=
  hypersurfaceHeightDeterminantError n +
    (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))

/-- Absence of an auxiliary polynomial implies the normalized
inequality with constructed geometry and exact Hilbert rank. -/
theorem hypersurface_no_auxiliary_normalized_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hdM : d ≤ M)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hrel : ∀ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 0 < s ∧ s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M ∧
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + Real.log (1 + Real.log H / (d : ℝ) ^ 2)) -
          hypersurfaceNormalizedError n) ≤
        Real.log B - ((n + 2 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) *
          Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, hs, hr, hc⟩ := hypersurface_no_auxiliary_height_comparison order f hf hd hdM hir
    H hH hcoeff hzB hrel
  refine ⟨s, hs, hr, ?_⟩
  have hnN : n + 1 + 1 = n + 2 := by omega
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hh := hypersurface_rank_comparison_normalized (r := n + 1) (by omega) hd hdM hr
    B |((order.leadingCoeff f : ℤ) : ℝ)| (1 + Real.log H / (d : ℝ) ^ 2)
    (hypersurfaceHeightDeterminantError n) (by simpa only [hnN, Nat.cast_add, Nat.cast_one,
      hnR] using hc)
  simpa only [hypersurfaceNormalizedError, hnN,
    Nat.cast_add, Nat.cast_one, hnR] using hh

end
end CCDN
