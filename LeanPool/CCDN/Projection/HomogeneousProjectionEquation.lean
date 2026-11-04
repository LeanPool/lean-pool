/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Projection.HomogeneousFilteredProjection
import LeanPool.CCDN.Projection.PlaneRelationSpace

/-! The principal equation of the image of a homogeneous linear
projection is homogeneous. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For a homogeneous ideal `I` and homogeneous linear forms `a`, the kernel of the projection by
`a` is closed under taking homogeneous components. -/
theorem projection_kernel_homogeneousComponent_mem
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K))
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (p : MvPolynomial σ K) (hp : p ∈ RingHom.ker (projectionCoordinateMap I a)) (N : ℕ) :
    homogeneousComponent N p ∈ RingHom.ker (projectionCoordinateMap I a) := by
  change (Ideal.Quotient.mk I) (aeval a (homogeneousComponent N p)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← homogeneousComponent_aeval_linear a ha]
  apply hI
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hp

/-- A nonzero generator of a principal ideal that is closed under homogeneous components is
homogeneous of its total degree. -/
theorem principal_generator_isHomogeneous
    {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneousIdeal I)
    (f : MvPolynomial σ K) (hf : f ≠ 0) (hgen : I = Ideal.span {f}) :
    f.IsHomogeneous f.totalDegree := by
  have hmem : f ∈ I := by rw [hgen]; exact Ideal.subset_span (Set.mem_singleton f)
  have ht := hI f hmem f.totalDegree
  rw [hgen, Ideal.mem_span_singleton] at ht
  obtain ⟨c, hc⟩ := eq_scalar_mul_of_dvd_of_totalDegree_le f
    (homogeneousComponent f.totalDegree f) hf ht
    (homogeneousComponent_isHomogeneous f.totalDegree f).totalDegree_le
  have hcne : c ≠ 0 := by
    intro hz
    apply homogeneousComponent_totalDegree_ne_zero hf
    rw [hc, hz, zero_smul]
  have hh := (homogeneousComponent_isHomogeneous f.totalDegree f).C_mul c⁻¹
  rw [hc] at hh
  rw [← smul_eq_C_mul] at hh
  simpa only [smul_smul, inv_mul_cancel₀ hcne, one_smul] using hh

/-- If the kernel of the projection of a homogeneous ideal by homogeneous linear forms is generated
by a nonzero polynomial `f`, then `f` is homogeneous of its total degree. -/
theorem homogeneous_projection_equation
    {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K))
    (hI : IsHomogeneousIdeal I)
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (f : MvPolynomial σ K) (hf : f ≠ 0)
    (hgen : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.IsHomogeneous f.totalDegree :=
  principal_generator_isHomogeneous _ (projection_kernel_homogeneousComponent_mem I hI a ha)
    f hf hgen

end
end CCDN
