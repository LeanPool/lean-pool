/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousChart
public import LeanPool.CCDN.Height.ProjectiveZeroLocus

/-! Affine coordinates on the standard open subset of projective space,
with injectivity and compatibility with homogeneous equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

/-- The affine coordinates `(x₁ / x₀, …, xₙ / x₀)` of a projective point `x`, computed from
its chosen representative; meaningful on the standard chart `x₀ ≠ 0`. -/
def projectiveAffineCoordinates {n : ℕ} (x : Projectivization K (Fin (n + 1) → K)) :
    Fin n → K := fun j => x.rep j.succ / x.rep 0

private lemma projectiveAffineCoordinates_normalization {n : ℕ}
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep 0 ≠ 0) :
    Fin.cons 1 (projectiveAffineCoordinates x) = (x.rep 0)⁻¹ • x.rep := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [hx]
  · simp [projectiveAffineCoordinates, div_eq_mul_inv, mul_comm]

/-- The vector `(1, a₁, …, aₙ)` is nonzero. -/
lemma affineCoordinateVector_ne_zero {n : ℕ} (a : Fin n → K) :
    (Fin.cons 1 a : Fin (n + 1) → K) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp at hh

private lemma projectiveAffineCoordinates_mk {n : ℕ}
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep 0 ≠ 0) :
    Projectivization.mk K (Fin.cons 1 (projectiveAffineCoordinates x))
      (affineCoordinateVector_ne_zero _) = x := by
  calc
    _ = Projectivization.mk K x.rep x.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨_, (projectiveAffineCoordinates_normalization x hx).symm⟩
    _ = x := x.mk_rep

/-- Projective points with nonzero first coordinate are determined by their affine
coordinates. -/
theorem projectiveAffineCoordinates_injective {n : ℕ}
    {x y : Projectivization K (Fin (n + 1) → K)}
    (hx : x.rep 0 ≠ 0) (hy : y.rep 0 ≠ 0)
    (hxy : projectiveAffineCoordinates x = projectiveAffineCoordinates y) : x = y := by
  have h := congrArg (fun a : Fin n → K => Projectivization.mk K (Fin.cons 1 a : Fin (n + 1) → K)
    (affineCoordinateVector_ne_zero a)) hxy
  rwa [projectiveAffineCoordinates_mk x hx, projectiveAffineCoordinates_mk y hy] at h

/-- If a projective point `x` with nonzero first coordinate lies on the zero locus of a
homogeneous polynomial `f`, then the dehomogenization of `f` vanishes at the affine coordinates
of `x`. -/
theorem projectiveAffineCoordinates_zero {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous d)
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep 0 ≠ 0)
    (hxf : x ∈ projectiveZeroLocus f) :
    eval (projectiveAffineCoordinates x) (affineChart n f) = 0 := by
  rw [affineChart_eval, projectiveAffineCoordinates_normalization x hx,
    homogeneous_eval_smul hf, show eval x.rep f = 0 from hxf, mul_zero]

/-- The point `[1 : a]` of projective space on the standard chart. -/
def affineProjectivePoint {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) :
    Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (Fin.cons 1 a) (affineCoordinateVector_ne_zero a)

/-- The map `a ↦ [1 : a]` from affine space to projective space is injective. -/
theorem affineProjectivePoint_injective {K : Type*} [Field K] (n : ℕ) :
    Function.Injective (@affineProjectivePoint K _ n) := by
  intro a b he
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp he
  have hc1 : (c : K) = 1 := by
    have h := congrFun hc 0
    change (c : K) * 1 = 1 at h
    simpa using h
  funext j
  have h := congrFun hc j.succ
  change (c : K) * b j = a j at h
  simpa [hc1] using h.symm

end
end CCDN
