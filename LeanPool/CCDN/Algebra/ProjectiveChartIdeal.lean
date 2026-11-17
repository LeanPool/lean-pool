/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveAffineChart
public import LeanPool.CCDN.Algebra.ProjectiveChartDegree

/-! The prime affine-chart ideal and the transport of projective
points and Hilbert degree to that ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. A homogeneous
polynomial `f` lies in `I` if and only if its dehomogenization `affineChart n f` lies in the
kernel of the coordinate-ratio map `projectiveChartCoordinateMap I q`. -/
theorem affineChart_mem_coordinate_kernel_iff {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    affineChart n f ∈ RingHom.ker (projectiveChartCoordinateMap I q) ↔ f ∈ I := by
  rw [RingHom.mem_ker, projectiveChartCoordinateMap_chart I q h0 f hf,
    mul_eq_zero_iff_left (pow_ne_zero _ (inv_ne_zero h0))]
  rw [show q ((Ideal.Quotient.mk I) f) = 0 ↔ (Ideal.Quotient.mk I) f = 0 from
    ⟨fun h => hq (by simpa using h), fun h => by rw [h, map_zero]⟩]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. A polynomial `f` of
total degree at most `M` lies in the kernel of the coordinate-ratio map
`projectiveChartCoordinateMap I q` if and only if its degree-`M` homogenization lies in `I`. -/
theorem coordinate_kernel_mem_iff_homogenize {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin n) K) (hf : f.totalDegree ≤ M) :
    f ∈ RingHom.ker (projectiveChartCoordinateMap I q) ↔ scaledHomogenize M 1 f ∈ I := by
  have h := affineChart_mem_coordinate_kernel_iff I q hq h0 (scaledHomogenize M 1 f)
    (scaledHomogenize_homogeneous 1 f hf)
  rwa [affineChart_scaledHomogenize_one] at h

private theorem projective_point_chart_vanishes {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (x : Projectivization K (Fin (n + 1) → K))
    (hx : x ∈ projectiveIdealZeroLocus I) (hx0 : x.rep 0 ≠ 0) :
    ∀ f ∈ RingHom.ker (projectiveChartCoordinateMap I q),
      eval (projectiveAffineCoordinates x) f = 0 := by
  intro f hf
  have hh := (coordinate_kernel_mem_iff_homogenize I q hq h0 f le_rfl).mp hf
  have hz := projectiveAffineCoordinates_zero (scaledHomogenize f.totalDegree 1 f)
    (scaledHomogenize_homogeneous 1 f le_rfl) x hx0 (projectiveIdealZeroLocus_rep hx _ hh)
  rwa [affineChart_scaledHomogenize_one] at hz

/-- The ideal of the standard affine chart `X₀ ≠ 0` of the projective variety cut out by a
homogeneous prime ideal `I`: the polynomials in the affine coordinates vanishing at the ratios
`Xⱼ / X₀` in the fraction field of the coordinate ring of `I`. -/
def projectiveChartIdeal {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime] :
    Ideal (MvPolynomial (Fin n) K) :=
  RingHom.ker (projectiveChartCoordinateMap I
    (IsScalarTower.toAlgHom K (MvPolynomial (Fin (n + 1)) K ⧸ I)
      (FractionRing (MvPolynomial (Fin (n + 1)) K ⧸ I))))

instance projectiveChartIdeal_isPrime {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime] :
    (projectiveChartIdeal I).IsPrime :=
  RingHom.ker_isPrime _

/-- If a prime ideal `I` not containing `X 0` defines a projective curve of degree `d`, then its
standard affine chart ideal defines an affine curve of degree `d`. -/
theorem projectiveChartIdeal_degree {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (hdegree : HasProjectiveCurveDegree I d) :
    HasAffineCurveDegree (projectiveChartIdeal I) d := by
  apply projective_chart_degree I _ (IsFractionRing.injective _ _) _ hdegree
  intro h
  exact hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h))

/-- If a projective point `x` on the zero locus of a prime ideal `I` (with `X 0 ∉ I`) has
nonzero first coordinate, then its affine coordinates lie on the zero locus of the standard
affine chart ideal of `I`. -/
theorem projectiveChartIdeal_point {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (hX : X 0 ∉ I)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) (hx0 : x.rep 0 ≠ 0) :
    projectiveAffineCoordinates x ∈ idealZeroLocus (projectiveChartIdeal I) := by
  apply projective_point_chart_vanishes I _ (IsFractionRing.injective _ _) _ x hx hx0
  intro h
  exact hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h))

end
end CCDN
