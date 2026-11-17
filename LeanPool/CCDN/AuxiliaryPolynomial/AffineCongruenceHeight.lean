/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Determinant.HypersurfaceDeterminantRank
public import LeanPool.CCDN.Height.CountingHypotheses
public import LeanPool.CCDN.Plane.IntegerPlaneLogHeight
import LeanPool.CCDN.AuxiliaryPolynomial.CongruenceBadPrimeCharge
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import LeanPool.CCDN.Determinant.AffineCongruenceDeterminant

/-! The affine congruence determinant bound with all bad-prime charges
controlled by the equation's coefficient height and congruence modulus. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The logarithmic bad-prime charge in the affine congruence determinant estimate for a form
of degree `d` in `m` variables with coefficient height at most `H`, where `Q` is the sum of
the logarithms of the congruence primes. -/
def congruenceHeightCharge (m d : ℕ) (H Q : ℝ) : ℝ :=
  Real.log (1 + 27 * (d : ℝ) ^ 4 *
    (hypersurfaceHeightConstant m * (1 + Real.log H / (d : ℝ) ^ 2)) + Q) +
      2 * mertensError + 1

/-- The logarithmic height and modulus are the only equation-dependent
errors in the affine smooth-congruence determinant estimate. -/
theorem affine_congruence_determinant_log_lower_height {n s N M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (G : Fin N → MvPolynomial (Fin (n + 2)) ℤ) (hG : ∀ j, (G j).totalDegree ≤ M)
    (x : Fin s → IntPoint (n + 2)) (hx : ∀ i, eval (x i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (x i) (G j)).map ((↑) : ℤ → ℚ)).row)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x) :
    hypersurfaceRankLowerBound n s f.totalDegree
        (congruenceHeightCharge (n + 3) f.totalDegree H (∑ p ∈ P, Real.log p)) +
      (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) *
        (∑ p ∈ P, Real.log p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (G j))) := by
  obtain ⟨bad, hbad, hbound⟩ := exists_affine_congruence_determinant_log_lower hs f hir hd
    G hG x hx hrows P a hres
  let F := scaledHomogenize f.totalDegree 1 f
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero _ one_ne_zero hf0
  have hFdegree : F.totalDegree = f.totalDegree :=
    (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree hF0
  have hFir : AbsolutelyIrreducible F :=
    (unscaledHomogenize_absolute_irreducible_iff f hf0).mpr hir
  have hheight : (integerCoefficientHeight F : ℝ) ≤ H := by
    rw [show F = scaledHomogenize f.totalDegree 1 f from rfl,
      integerCoefficientHeight_scaledHomogenize_one]
    exact integerCoefficientHeight_le f (by linarith) hcoeff
  have hc := hypersurface_and_congruence_prime_charge F hFir (hFdegree ▸ hd) H hH
    (fun e => (coefficient_abs_le_integerCoefficientHeight F e).trans hheight) bad P
    (fun p hp => by simpa only [hFdegree] using (hbad p).mp hp) hres.prime
  change (∑ p ∈ bad ∪ P, Real.log p / p) ≤
    congruenceHeightCharge (n + 3) F.totalDegree H (∑ p ∈ P, Real.log p) at hc
  rw [hFdegree] at hc
  have hfactor : 0 ≤ ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) := by positivity
  apply le_trans ?_ hbound
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ hfactor
    have hcharge := mul_le_mul_of_nonneg_left hc (show 0 ≤ (n + 1 : ℝ) by positivity)
    linarith
  · exact le_rfl

end
end CCDN
