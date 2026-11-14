/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.HypersurfaceDeterminantRank
public import LeanPool.CCDN.Height.CountingHypotheses
public import LeanPool.CCDN.Plane.IntegerPlaneLogHeight
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates

/-! The global determinant bound in higher dimension, with its reduction
hypotheses verified by the bad-prime set and its coefficient-height control. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The rank-cutoff determinant estimate with the exact constructed bad-prime
set. This is the common-degree maximal-minor form of CCDN Proposition 3.2.6. -/
theorem exists_hypersurface_determinant_log_lower
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z) :
    ∃ bad : Finset ℕ,
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      hypersurfaceRankLowerBound n s d (∑ p ∈ bad, Real.log p / p) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  obtain ⟨bad, hmem⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  exact ⟨bad, hmem, hypersurface_determinant_log_lower_at_rank hs f hf hd F hev.isHomogeneous z
    hev.primitive hev.eval_eq_zero hev.rows_linearIndependent
    bad fun p _ hp hcut => hasGoodReduction_of_not_mem hmem p (mem_sdiff.mp hp).2 hcut⟩

/-- The height-dependent error contains only dimension constants. -/
def hypersurfaceHeightDeterminantError (n : ℕ) : ℝ :=
  hypersurfaceDeterminantError n +
    (n + 1 : ℝ) * (Real.log (hypersurfaceHeightConstant (n + 3)) + 2 * mertensError + 1)

/-- The full higher-dimensional logarithmic determinant lower bound,
including the local counts and the geometric bad-prime charge. -/
theorem hypersurface_determinant_log_lower_height
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z) :
    factorialRoot n / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + Real.log (1 + Real.log H / (d : ℝ) ^ 2)) -
          hypersurfaceHeightDeterminantError n) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  classical
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  have hdeg : f.totalDegree = d := hf.totalDegree hf0
  obtain ⟨bad, hmem, hcharge⟩ :=
    exists_fin_hypersurface_bad_prime_charge f hir (hdeg ▸ hd) H hH hcoeff
  rw [hdeg] at hmem hcharge
  have hred (p : ℕ) [Fact p.Prime]
      (hp : p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad)
      (hcut : stepanovThreshold (d : ℝ) < p) :
      HasGoodReduction f p :=
    hasGoodReduction_of_not_mem hmem p (mem_sdiff.mp hp).2 hcut
  have hlower := hypersurface_determinant_log_lower_at_rank hs f hf hd F hev.isHomogeneous z
    hev.primitive hev.eval_eq_zero hev.rows_linearIndependent bad hred
  unfold hypersurfaceRankLowerBound at hlower
  have hc : 0 < hypersurfaceHeightConstant (n + 3) :=
    zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le _)
  have hh : 0 < 1 + Real.log H / (d : ℝ) ^ 2 := by
    have := div_nonneg (Real.log_nonneg hH) (sq_nonneg (d : ℝ))
    linarith
  rw [Real.log_mul hc.ne' hh.ne'] at hcharge
  have hcost := mul_le_mul_of_nonneg_left hcharge
    (show 0 ≤ ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) * (n + 1 : ℝ) by positivity)
  unfold hypersurfaceHeightDeterminantError
  nlinarith

end
end CCDN
