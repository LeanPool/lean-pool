/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.PDeriv
import LeanPool.CCDN.Determinant.PlaneSingularities
import LeanPool.CCDN.Determinant.SingularDeterminant
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.ForMathlib.MvPolynomialDerivative
import LeanPool.CCDN.Hypersurface.NonabsoluteHypersurfaceCount

/-! The singular locus of an irreducible rational hypersurface has a
coefficient-uniform codimension-two integer point bound. A nonzero partial
derivative gives the proper intersection used in the count. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The rational points of the singular locus of the hypersurface `f = 0`: the common zeros of
`f` and all its partial derivatives. -/
def singularHypersurfaceLocus {n : ℕ} (f : MvPolynomial (Fin n) ℚ) :
    Set (RatPoint n) :=
  {x | eval x f = 0 ∧ ∀ j, eval x (pderiv j f) = 0}

private theorem exists_proper_partial_derivative {K σ : Type*}
    [Field K] [CharZero K] [Finite σ]
    (f : MvPolynomial σ K) (hir : Irreducible f) :
    ∃ j, pderiv j f ≠ 0 ∧ ¬ f ∣ pderiv j f ∧
      (pderiv j f).totalDegree < f.totalDegree := by
  classical
  let := Fintype.ofFinite σ
  have hd := MvPolynomial.totalDegree_pos_of_irreducible hir
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hd fun n hn _ ↦ Nat.cast_ne_zero.mpr hn.ne'
  have hdeg : (pderiv j f).totalDegree < f.totalDegree := by
    have := pderiv_totalDegree_le f j
    omega
  exact ⟨j, hj, not_dvd_pderiv_of_pderiv_ne_zero hir.ne_zero hj, hdeg⟩

private theorem singular_hypersurface_count_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℚ) (hir : Irreducible f)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n := by
  obtain ⟨j, _, hproper, hdeg⟩ := exists_proper_partial_derivative f hir
  have hsub : singularHypersurfaceLocus f ⊆ zeroLocus f ∩ zeroLocus (pderiv j f) :=
    fun x hx => ⟨hx.1, hx.2 j⟩
  exact (Nat.cast_le.mpr (count_mono hsub le_rfl)).trans
    (proper_intersection_count_le_box f (pderiv j f) hir.prime hproper le_rfl hdeg.le hB)

/-- The singular locus of an irreducible rational hypersurface in `n + 2` variables has at most
`(3 * (n + 2)) ^ n * deg f ^ 2 * B ^ n` integral points of height at most `B`, for every
`B ≥ 1`. -/
theorem singular_hypersurface_dimension_growth {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℚ) (hir : Irreducible f)
    {B : ℝ} (hB : 1 ≤ B) :
    (count (singularHypersurfaceLocus f) B : ℝ) ≤
      (3 * (n + 2) : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * B ^ n := by
  calc
    _ ≤ (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) ^ n :=
      singular_hypersurface_count_le f hir (by linarith)
    _ ≤ (n + 2 : ℝ) ^ n * (f.totalDegree : ℝ) ^ 2 * (3 * B) ^ n := by
      gcongr
      linarith
    _ = _ := by simp only [mul_pow]; ring

end
end CCDN
