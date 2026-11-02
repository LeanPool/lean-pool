/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.AffineTranslation
public import LeanPool.CCDN.Hypersurface.GraphHyperplaneRestriction
import LeanPool.CCDN.AuxiliaryPolynomial.AffineLeadingTranslation

/-! Parallel affine slices preserve the good leading hyperplane section.
Rational restriction equations can then be replaced by integer
polynomials without changing their zero sets or total degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The `K`-algebra automorphism of `K[x_none, x_0, …, x_{n-1}]` translating the distinguished
coordinate `x_none` by the constant `c` and fixing the other coordinates. -/
def optionCoordinateShift {K : Type*} [CommRing K] {n : ℕ} (c : K) :
    MvPolynomial (Option (Fin n)) K →ₐ[K] MvPolynomial (Option (Fin n)) K :=
  aeval (fun i => Option.elim i (X none + C c) (fun j => X (some j)))

private lemma optionCoordinateShift_rename {K : Type*} [CommRing K] {n : ℕ}
    (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    rename (finSuccEquiv n).symm (optionCoordinateShift c f) =
      affineTranslation K (Fin.cons c (fun _ => 0)) (rename (finSuccEquiv n).symm f) := by
  have he : (rename (finSuccEquiv n).symm).toRingHom.comp (optionCoordinateShift c).toRingHom =
      (affineTranslation K (Fin.cons c (fun _ : Fin n => 0))).toRingHom.comp
        (rename (finSuccEquiv n).symm).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [optionCoordinateShift, affineTranslation]
    · intro i
      cases i <;> simp [optionCoordinateShift, affineTranslation]
  exact RingHom.congr_fun he f

private lemma optionCoordinateShift_degree {K : Type*} [CommRing K] [Nontrivial K] {n : ℕ}
    (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    (optionCoordinateShift c f).totalDegree = f.totalDegree := by
  have hh := congrArg totalDegree (optionCoordinateShift_rename c f)
  simpa only [← renameEquiv_apply, totalDegree_renameEquiv, affineTranslation_totalDegree] using hh

private lemma optionCoordinateShift_top {K : Type*} [CommRing K] [Nontrivial K] {n : ℕ}
    (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    homogeneousComponent f.totalDegree (optionCoordinateShift c f) =
      homogeneousComponent f.totalDegree f := by
  apply rename_injective (finSuccEquiv n).symm (finSuccEquiv n).symm.injective
  rw [rename_homogeneousComponent, optionCoordinateShift_rename, rename_homogeneousComponent]
  simpa only [affineTranslation_totalDegree, ← renameEquiv_apply, totalDegree_renameEquiv] using
    affineTranslation_leading_homogeneousComponent (Fin.cons c (fun _ : Fin n => 0))
      (rename (finSuccEquiv n).symm f)

private lemma optionCoordinateShift_eval {K : Type*} [CommRing K] {n : ℕ}
    (c : K) (x : Option (Fin n) → K) (f : MvPolynomial (Option (Fin n)) K) :
    eval x (optionCoordinateShift c f) =
      eval (fun i => Option.elim i (x none + c) (fun j => x (some j))) f := by
  have he : (eval x).comp (optionCoordinateShift c).toRingHom =
      eval (fun i => Option.elim i (x none + c) (fun j => x (some j))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [optionCoordinateShift]
    · intro i
      cases i <;> simp [optionCoordinateShift]
  exact RingHom.congr_fun he f

/-- The restriction of `f` to the affine hyperplane `x_none = ∑ a j * x j + c`, written as a
polynomial in the remaining coordinates `x j`. -/
def affineGraphHyperplaneSlice {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → K) (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    MvPolynomial (Fin n) K :=
  graphHyperplaneRestriction a (optionCoordinateShift c f)

/-- Evaluating the affine slice `affineGraphHyperplaneSlice a c f` at `x` is evaluating `f` at the
point of the hyperplane `x_none = ∑ a j * x j + c` lying over `x`. -/
lemma affineGraphHyperplaneSlice_eval {K : Type*} [CommRing K] {n : ℕ}
    (a : Fin n → K) (c : K) (f : MvPolynomial (Option (Fin n)) K) (x : Fin n → K) :
    eval x (affineGraphHyperplaneSlice a c f) =
      eval (fun i => Option.elim i ((∑ j, a j * x j) + c) x) f := by
  rw [affineGraphHyperplaneSlice, graphHyperplaneRestriction_eval, optionCoordinateShift_eval]
  rfl

/-- The degree-`f.totalDegree` component of an affine slice of `f` is the restriction of the top
form of `f` to the parallel linear hyperplane `x_none = ∑ a j * x j`. -/
lemma affineGraphHyperplaneSlice_top {K : Type*} [CommRing K] [Nontrivial K] {n : ℕ}
    (a : Fin n → K) (c : K) (f : MvPolynomial (Option (Fin n)) K) :
    homogeneousComponent f.totalDegree (affineGraphHyperplaneSlice a c f) =
      graphHyperplaneRestriction a (homogeneousComponent f.totalDegree f) := by
  rw [affineGraphHyperplaneSlice, ← graphHyperplaneRestriction_homogeneousComponent,
    optionCoordinateShift_top]

/-- A nonzero restriction of the top form prevents degree loss at every
parallel affine level. -/
theorem affineGraphHyperplaneSlice_degree {K : Type*} [Field K] {n : ℕ}
    (a : Fin n → K) (c : K) (f : MvPolynomial (Option (Fin n)) K)
    (htop : graphHyperplaneRestriction a (homogeneousComponent f.totalDegree f) ≠ 0) :
    (affineGraphHyperplaneSlice a c f).totalDegree = f.totalDegree := by
  apply le_antisymm
  · exact (graphHyperplaneRestriction_totalDegree_le _ _).trans_eq
      (optionCoordinateShift_degree c f)
  · by_contra h
    have hz := homogeneousComponent_eq_zero f.totalDegree
      (affineGraphHyperplaneSlice a c f) (by omega)
    rw [affineGraphHyperplaneSlice_top] at hz
    exact htop hz

end
end CCDN
