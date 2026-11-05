/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.PolynomialComparison
import LeanPool.CCDN.Hilbert.PrincipalHilbertPolynomial
import LeanPool.CCDN.Projection.HilbertProjectionKernel

/-! Degree bounds for hypersurface equations of linear projections.
The degree is bounded by the factorial-normalized leading coefficient of
the original quotient's filtered Hilbert polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem hypersurface_projection_equation_degree_le
    {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ}
    (I : Ideal (MvPolynomial τ K)) (hI : I ≠ ⊤)
    (a : Fin (n + 1) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I n d)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hfdeg : 0 < f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree ≤ d := by
  have hp : Ideal.span {f} ≠ ⊤ := by
    rw [← hker]
    let : Nontrivial (MvPolynomial τ K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    exact RingHom.ker_ne_top _
  have hh := filteredHilbertPolynomial_leadingCoeff_le (Ideal.span {f}) I hp hI
    ((principal_filteredHilbertPolynomial_natDegree f hf hfdeg).trans hdimdeg.natDegree_eq.symm)
    (fun N => by
      rw [← hker]
      exact linear_projection_filtered_finrank_le I a ha N)
  rw [principal_filteredHilbertPolynomial_leadingCoeff f hf hfdeg, hdimdeg.leadingCoeff_eq] at hh
  have hfac : (0 : ℚ) < n.factorial := by positivity
  exact_mod_cast (div_le_div_iff_of_pos_right hfac).mp hh

/-- The equation and its degree bound are constructed from the projection. -/
theorem exists_hypersurface_projection_equation_degree_le
    {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ}
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin (n + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I n d)
    (b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hb : ∀ i, (b i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i))) :
    ∃ f : MvPolynomial (Fin (n + 2)) K, Irreducible f ∧
      0 < f.totalDegree ∧ f.totalDegree ≤ d ∧
      RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
  obtain ⟨f, hf, hker⟩ := exists_hypersurface_projection_equation I a ha
    (by rw [hdimdeg.natDegree_eq]; omega) b hb hi
  have hfdeg : 0 < f.totalDegree :=
    totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit
  exact ⟨f, hf, hfdeg, hypersurface_projection_equation_degree_le I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›) a ha d hdimdeg f hf.ne_zero hfdeg hker, hker⟩

end
end CCDN
