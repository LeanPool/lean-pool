/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveClosureIdeal
public import LeanPool.CCDN.Hilbert.LinearProjectionFiltration
import LeanPool.CCDN.Algebra.ProjectionScalarExtension
import LeanPool.CCDN.Projection.HomogeneousFilteredProjection

/-! Homogenizing a linear affine projection while retaining its homogenizing
coordinate gives the projective closure of its affine image ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The homogenization of a projection by forms `a`: the forms `X 0, a 0, a 1, …` on the projective
coordinates, which keep the homogenizing coordinate `X 0` and shift the variables of each `a i`. -/
def closureProjectionCoordinates {K : Type*} [Field K] {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K) :
    Fin (m + 1) → MvPolynomial (Fin (n + 1)) K :=
  Fin.cons (X 0) (fun i => rename Fin.succ (a i))

/-- If all the forms `a i` are homogeneous linear, then so are their closure projection coordinates.
-/
lemma closureProjectionCoordinates_homogeneous {K : Type*} [Field K] {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1) (i : Fin (m + 1)) :
    (closureProjectionCoordinates a i).IsHomogeneous 1 := by
  refine Fin.cases (isHomogeneous_X K _) (fun j => ?_) i
  exact (ha j).rename_isHomogeneous

/-- Dehomogenizing at `X 0 = 1` a polynomial not involving `X 0` recovers the original polynomial.
-/
lemma affineChart_rename_succ {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) :
    affineChart n (rename Fin.succ f) = f := by
  have h : (affineChart (K := K) n).comp
      (rename (R := K) Fin.succ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart]
    · intro i
      simp [affineChart]
  exact RingHom.congr_fun h f

/-- Dehomogenization at `X 0 = 1` intertwines substitution of the closure projection coordinates
with substitution of the original forms `a`. -/
lemma affineChart_aeval_closureProjectionCoordinates
    {K : Type*} [Field K] {m n : ℕ}
    (a : Fin m → MvPolynomial (Fin n) K)
    (f : MvPolynomial (Fin (m + 1)) K) :
    affineChart n (aeval (closureProjectionCoordinates a) f) =
      aeval a (affineChart m f) := by
  have h : (affineChart (K := K) n).comp (aeval (closureProjectionCoordinates a)).toRingHom =
      (aeval (R := K) a).toRingHom.comp (affineChart (K := K) m) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineChart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [closureProjectionCoordinates, affineChart]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          aeval_X, closureProjectionCoordinates, Fin.cons_succ,
          affineChart_rename_succ]
        simp [affineChart]
  exact RingHom.congr_fun h f

/-- For homogeneous linear forms `a`, the projective closure of the kernel of the projection of
`I` by `a` is the kernel of the projection of the projective closure of `I` by the closure
coordinates `X 0, a 0, a 1, …`; this is an equality of ideals, not merely of zero sets. -/
theorem projectiveClosureIdeal_projection_kernel
    {K : Type*} [Field K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1) :
    projectiveClosureIdeal (RingHom.ker (projectionCoordinateMap I a)) =
      RingHom.ker (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a)) := by
  ext f
  rw [mem_projectionCoordinateMap_ker, mem_projectiveClosureIdeal_iff,
    mem_projectiveClosureIdeal_iff]
  simp only [homogeneousComponent_aeval_linear _
    (closureProjectionCoordinates_homogeneous a ha),
    affineChart_aeval_closureProjectionCoordinates,
    mem_projectionCoordinateMap_ker]

end
end CCDN
