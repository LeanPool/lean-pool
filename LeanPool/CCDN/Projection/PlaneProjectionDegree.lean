/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.Algebraic.Defs
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.AffineCurveDegree
import LeanPool.CCDN.Hilbert.PlaneHilbert
import LeanPool.CCDN.Plane.NonabsolutePlaneCount
import LeanPool.CCDN.Projection.PlaneProjectionKernel

/-! The irreducible image equation has degree at most the original affine
Hilbert degree. This is an upper bound; the degree need not be preserved. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A principal image equation of a linear projection has degree at most the
source's affine Hilbert degree. -/
theorem plane_projection_equation_degree_le {K τ : Type*} [Field K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (d : ℕ)
    (hdegree : HasFilteredCurveDegree I d)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree ≤ d := by
  classical
  let := Fintype.ofFinite τ
  apply eventual_linear_slope_le
    (fun M => Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) M))
    (fun M => Module.finrank K (filteredCoordinateSpace I M)) f.totalDegree d
    ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
      fun M hM => principal_plane_hilbert_function f hf hM⟩ hdegree
  intro M
  rw [← hker]
  exact linear_projection_filtered_finrank_le I a ha M

/-- A linear plane projection with a transcendental coordinate has an
irreducible equation of positive degree at most d and no extra kernel relations. -/
theorem exists_plane_projection_equation_degree_le {K τ : Type*} [Field K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (j : Fin 2) (hj : Transcendental K ((Ideal.Quotient.mk I) (a j))) :
    ∃ f : MvPolynomial (Fin 2) K, Irreducible f ∧ 0 < f.totalDegree ∧ f.totalDegree ≤ d ∧
      ∀ g, aeval a g ∈ I ↔ f ∣ g := by
  classical
  let := Fintype.ofFinite τ
  obtain ⟨f, hf, hker⟩ := exists_plane_projection_equation I a ha d hdegree j hj
  refine ⟨f, hf, totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit,
    plane_projection_equation_degree_le I a ha d hdegree f hf.ne_zero hker, ?_⟩
  intro g
  have hh : aeval a g ∈ I ↔ g ∈ RingHom.ker (projectionCoordinateMap I a) := by
    change _ ↔ (Ideal.Quotient.mk I) (aeval a g) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  rw [hh, hker, Ideal.mem_span_singleton]

end
end CCDN
