/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.AffineNonzeroConstant
import LeanPool.CCDN.Algebra.PrimitiveNormalization
import LeanPool.CCDN.Plane.AffinePlaneAssembly

/-! Rational equations and the coefficient-uniform affine plane bound.
The sharp finite-field estimate is stated as a proposition, not an axiom. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Real

/-- The finite-field counting obligation `PlaneResidueCountBound` for every plane equation
of positive degree, with one absolute constant. `planeResidueBound` discharges it with
`C = planeResidueConstant`. -/
def PlaneResidueBound (C : ℝ) : Prop :=
  ∀ f : MvPolynomial (Fin 2) ℤ, 0 < f.totalDegree → PlaneResidueCountBound C f.totalDegree f

/-- If an integer polynomial `g` is a nonzero rational multiple of a rational polynomial `f` that
is irreducible over a field `F` of characteristic zero, then `g` is irreducible over `F`. -/
lemma rational_scalar_model_irreducible_charZero {F σ : Type*} [Field F] [CharZero F]
    {f : MvPolynomial σ ℚ} {g : MvPolynomial σ ℤ} {a : ℚ} (ha : a ≠ 0)
    (he : MvPolynomial.map (Int.castRingHom ℚ) g = C a * f)
    (hf : Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) :
    Irreducible (MvPolynomial.map (Int.castRingHom F) g) := by
  have hh := congrArg (MvPolynomial.map (algebraMap ℚ F)) he
  rw [map_map, map_mul, map_C] at hh
  have hc : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = Int.castRingHom F := by ext; simp
  rw [hc] at hh
  rw [hh]
  have hu : IsUnit (C ((algebraMap ℚ F) a) : MvPolynomial σ F) :=
    ((isUnit_iff_ne_zero.mpr ha).map (algebraMap ℚ F)).map C
  exact (irreducible_isUnit_mul hu).mpr hf

/-- A rational absolutely irreducible equation has the affine bound for every
real B>=1. Primitive normalization and every analytic reduction are proved;
the sharp finite-field bound is the one explicit counting hypothesis. -/
theorem count_rational_plane_of_residue_bound
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (f : MvPolynomial (Fin 2) ℚ)
    (hir : Irreducible (MvPolynomial.map (algebraMap ℚ F) f)) (hd : 0 < f.totalDegree)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C) (hres : PlaneResidueBound C) :
    (count (zeroLocus f) B : ℝ) ≤
      (2 * Real.exp 1 * affineNonzeroConstantBound C) * curveBound f.totalDegree B := by
  have hf0 : f ≠ 0 := fun h => hir.ne_zero (by simp [h])
  obtain ⟨g, a, hg, ha, he⟩ := exists_primitive_integer_model f hf0
  have hdeg := rational_scalar_model_degree ha hf0 he
  have hgi := rational_scalar_model_irreducible_charZero ha he hir
  have hgd : 0 < g.totalDegree := by rwa [hdeg]
  have hzero : zeroLocus (MvPolynomial.map (Int.castRingHom ℚ) g) = zeroLocus f := by
    ext x
    exact rational_scalar_model_zero_iff ha he x
  have h := count_plane_of_residue_bound g hg hgi hgd hB hC (hres g hgd)
  rwa [hzero, hdeg] at h

end
end CCDN
