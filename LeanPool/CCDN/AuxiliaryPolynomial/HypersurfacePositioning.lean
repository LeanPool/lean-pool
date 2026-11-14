/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.CharZeroOrGT
public import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceAffineCoordinates
public import LeanPool.CCDN.ForMathlib.Matrix
public import LeanPool.CCDN.Noether.GenericPlaneIrreducibility
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceFullOuterDegree
import LeanPool.CCDN.AuxiliaryPolynomial.HypersurfaceGoodDirection
import LeanPool.CCDN.Determinant.GenericPlaneMinor
import LeanPool.CCDN.Determinant.HypersurfaceSmoothPoint

/-! Full-degree monic positioning of an irreducible hypersurface at a
smooth point, using an invertible affine change and a nonzero scalar. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Normalize the leading scalar of the explicit affine coordinate change. -/
def normalizedHypersurfaceCoordinates {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    MvPolynomial (Option σ) K :=
  C (eval b (homogeneousComponent f.totalDegree f))⁻¹ * hypersurfaceAffineCoordinates a b hb f

/-- If the leading form of `f` does not vanish at the direction `b`, then the normalized affine
coordinate change of `f` is monic as a polynomial in the distinguished variable `none`. -/
lemma normalizedHypersurfaceCoordinates_monic {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff, hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir,
    hypersurfaceAffineCoordinates_top_coefficient, ← map_mul, inv_mul_cancel₀ hdir, map_one]

private lemma normalizedHypersurfaceCoordinates_natDegree {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).natDegree =
      f.totalDegree := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C,
    Polynomial.natDegree_C_mul_of_isUnit ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)]
  exact hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir

private lemma normalizedHypersurfaceCoordinates_totalDegree_le {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    (normalizedHypersurfaceCoordinates a b hb f).totalDegree ≤ f.totalDegree := by
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact hypersurfaceAffineCoordinates_totalDegree_le a b hb f)

private lemma normalizedHypersurfaceCoordinates_irreducible {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hf : Irreducible f) (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    Irreducible (normalizedHypersurfaceCoordinates a b hb f) := by
  apply (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)).mpr
  exact (MulEquiv.irreducible_iff (f := hypersurfaceAffineCoordinates a b hb)).mpr hf

private lemma normalizedHypersurfaceCoordinates_eval_zero {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hz : eval a f = 0) :
    eval (0 : Option σ → K) (normalizedHypersurfaceCoordinates a b hb f) = 0 := by
  rw [normalizedHypersurfaceCoordinates, map_mul, hypersurfaceAffineCoordinates_eval_zero, hz,
    mul_zero]

private lemma normalizedHypersurfaceCoordinates_partial_ne_zero {K σ : Type*} [Field K] [Fintype σ]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0)
    (ht : (∑ i, eval a (pderiv i f) * b i) ≠ 0) :
    eval (0 : Option σ → K) (pderiv none (normalizedHypersurfaceCoordinates a b hb f)) ≠ 0 := by
  rw [normalizedHypersurfaceCoordinates, pderiv_C_mul, map_mul, eval_C,
    hypersurfaceAffineCoordinates_partial_zero]
  exact mul_ne_zero (inv_ne_zero hdir) ht

/-- The equation `g` is in position for the generic-plane minor: it is irreducible, monic of
degree `d` in the distinguished variable `none`, of total degree at most `d`, and passes through
the origin, where its derivative in the distinguished variable does not vanish. -/
structure IsMonicSmoothAtOrigin {K σ : Type*} [Field K] (g : MvPolynomial (Option σ) K)
    (d : ℕ) : Prop where
  /-- The equation is irreducible. -/
  irreducible : Irreducible g
  /-- The equation is monic in the distinguished variable `none`. -/
  monic : (optionEquivLeft K σ g).Monic
  /-- The equation has degree `d` in the distinguished variable `none`. -/
  natDegree_eq : (optionEquivLeft K σ g).natDegree = d
  /-- The equation has total degree at most `d`. -/
  totalDegree_le : g.totalDegree ≤ d
  /-- The equation vanishes at the origin. -/
  eval_zero : eval (0 : Option σ → K) g = 0
  /-- The partial derivative in the distinguished variable `none` does not vanish at the
  origin. -/
  pderiv_ne_zero : eval (0 : Option σ → K) (pderiv none g) ≠ 0

/-- Smooth-point existence and direction avoidance discharge all positioning
hypotheses: the coordinates and the nonzero scalar are actually constructed. -/
theorem exists_monic_smooth_hypersurface_coordinates
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K f.totalDegree) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      IsMonicSmoothAtOrigin (normalizedHypersurfaceCoordinates a b hb f) f.totalDegree := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨a, j, ha, hj⟩ := exists_smooth_hypersurface_point_of_degree_lt_char f hf hpos hchar
  obtain ⟨b, hb, hdir, ht⟩ :=
    exists_good_hypersurface_direction_with_coordinate f hf.ne_zero a j hj none
  exact ⟨a, b, hb, hdir, normalizedHypersurfaceCoordinates_irreducible a b hb f hf hdir,
    normalizedHypersurfaceCoordinates_monic a b hb f hdir,
    normalizedHypersurfaceCoordinates_natDegree a b hb f hdir,
    normalizedHypersurfaceCoordinates_totalDegree_le a b hb f,
    normalizedHypersurfaceCoordinates_eval_zero a b hb f ha,
    normalizedHypersurfaceCoordinates_partial_ne_zero a b hb f hdir ht⟩

/-- Every irreducible positive-degree hypersurface in characteristic zero or larger
than 2*d^2 has an explicitly positioned generic-plane family with a nonzero slope minor. -/
theorem exists_positioned_genericPlane_minor
    {K σ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (closedFormCoefficientMatrix f.totalDegree
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          (2 * f.totalDegree ^ 2 - 1) := by
  classical
  let := Fintype.ofFinite σ
  obtain ⟨a, b, hb, hdir, hg⟩ := exists_monic_smooth_hypersurface_coordinates f hf hpos
    (hchar.mono (by nlinarith [Nat.le_mul_self f.totalDegree]))
  exact ⟨a, b, hb, hdir, exists_genericPlane_minor f.totalDegree hpos _ hg.irreducible hg.monic
    hg.natDegree_eq hg.totalDegree_le hchar hg.eval_zero hg.pderiv_ne_zero⟩

end
end CCDN
