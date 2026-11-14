/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Height.Box
public import LeanPool.CCDN.Height.IntegerCoefficientHeight
public import LeanPool.CCDN.Noether.ClosedFormHeight
public import LeanPool.CCDN.Plane.FiniteFieldBadPlanes
import LeanPool.CCDN.Height.PolynomialBoxHeight
import LeanPool.CCDN.Noether.UniversalPlaneSpecialization
import LeanPool.CCDN.Plane.GridHeight

/-! Coefficient height of an integer plane section with bounded
parameters, and the resulting bound on the universal bad-prime witness. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Taking plane sections commutes with mapping coefficients along a ring homomorphism `φ`: the
section of `map φ f` at `φ ∘ v` is the coefficient-wise image of the section of `f` at `v`. -/
lemma universalPlaneSection_map {R S σ : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial σ R) (v : PlaneParameters σ → R) :
    universalPlaneSection (MvPolynomial.map φ f) (φ ∘ v) =
      bivariateMap φ (universalPlaneSection f v) := by
  unfold universalPlaneSection
  rw [universalPlanePolynomial_map, ← bivariateMap_comp_apply,
    ← bivariateMap_comp_apply]
  congr 2
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- Height supplied by interpolation on the plane grid. -/
def integerPlaneHeight (m d : ℕ) (H A : ℝ) : ℝ :=
  ((d : ℝ) + 1) ^ (2 * (d + 1)) *
    (((d : ℝ) + 1) ^ m * H * (A * (1 + 2 * d)) ^ d)

/-- Each coefficient of a bounded integer plane section is bounded explicitly
in terms of the original coefficient height, degree and ambient dimension. -/
theorem integer_plane_section_coefficient_bound {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℤ) (H A : ℝ) (hH : 0 ≤ H) (hA : 1 ≤ A)
    (hf : CoefficientHeightLE f H)
    (v : PlaneParameters σ → ℤ) (hv : InBox v A) :
    BivariateCoefficientBound (universalPlaneSection f v)
      (integerPlaneHeight (Fintype.card σ) f.totalDegree H A) := by
  let φ := Int.castRingHom ℝ
  let g := universalPlaneSection (MvPolynomial.map φ f) (φ ∘ v)
  have he : g = bivariateMap φ (universalPlaneSection f v) :=
    universalPlaneSection_map φ f v
  have hd : bivariateTotalDegree g ≤ f.totalDegree := by
    rw [he]
    exact (bivariateTotalDegree_map_le _ _).trans
      (universalPlanePolynomial_specialization_totalDegree f (eval v))
  have hB : 1 ≤ A * (1 + 2 * (f.totalDegree : ℝ)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) f.totalDegree]
  have hgrid (x y : ℕ) (hx : x ≤ f.totalDegree) (hy : y ≤ f.totalDegree) :
      |(Polynomial.map (Polynomial.evalRingHom (y : ℝ)) g).eval (x : ℝ)| ≤
        ((f.totalDegree : ℝ) + 1) ^ Fintype.card σ * H *
          (A * (1 + 2 * f.totalDegree)) ^ f.totalDegree := by
    change |bivariateEval (x : ℝ) (y : ℝ) g| ≤ _
    dsimp only [g]
    rw [universalPlaneSection_eval, eval_map]
    apply polynomial_eval₂_box_bound f H _ hH hB hf
    intro i
    have hxR : (x : ℝ) ≤ f.totalDegree := by exact_mod_cast hx
    have hyR : (y : ℝ) ≤ f.totalDegree := by exact_mod_cast hy
    change |(v (i,0) : ℝ) + (v (i,1) : ℝ) * x + (v (i,2) : ℝ) * y| ≤ _
    calc
      _ ≤ |(v (i,0) : ℝ)| + |(v (i,1) : ℝ)| * x + |(v (i,2) : ℝ)| * y := by
        simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) x),
          abs_of_nonneg (Nat.cast_nonneg (α := ℝ) y)] using
          (abs_add_le ((v (i,0) : ℝ) + (v (i,1) : ℝ) * x) ((v (i,2) : ℝ) * y)).trans
            (add_le_add (abs_add_le (v (i,0) : ℝ) ((v (i,1) : ℝ) * x)) le_rfl)
      _ ≤ A + A * x + A * y := by
        gcongr
        · exact hv _
        · exact hv _
        · exact hv _
      _ ≤ A * (1 + 2 * f.totalDegree) := by nlinarith
  intro i j
  have hh := bivariate_coefficient_bound_of_integer_grid g hd
    (by positivity) hgrid i j
  rw [he, bivariateMap_coeff] at hh
  exact hh

end
end CCDN
