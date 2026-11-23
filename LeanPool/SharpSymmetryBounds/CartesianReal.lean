/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.CartesianCoordinates

/-!
# Real Cartesian equations

Real plane polynomials, their Cartesian zero sets and geometric irreducibility, with the bounds
for real Cartesian input.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Real polynomials in the Cartesian coordinates `x`, `y`. -/
abbrev RPoly := MvPolynomial (Fin 2) ℝ

/-- A real Cartesian polynomial written in the complex coordinates `z`, `conj z`. -/
noncomputable def complexifyReal (f : RPoly) : BPoly :=
  complexify (map Complex.ofRealHom f)

/-- The real zero set `{x + i y | f(x, y) = 0}` of a real Cartesian polynomial, inside `ℂ`. -/
def cartesianLocus (f : RPoly) : Set ℂ :=
  {z | eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f = 0}

/-- Geometric irreducibility, not just irreducibility over the reals. -/
def GeometricallyIrreducible (f : RPoly) : Prop :=
  Irreducible (map Complex.ofRealHom f)

lemma real_map_degree (f : RPoly) : (map Complex.ofRealHom f).totalDegree = f.totalDegree := by
  simp only [totalDegree,
    support_map_of_injective f (f := Complex.ofRealHom) Complex.ofReal_injective]

lemma complexifyReal_degree (f : RPoly) : (complexifyReal f).totalDegree = f.totalDegree := by
  rw [complexifyReal, complexify_degree, real_map_degree]

lemma complexifyReal_irreducible {f : RPoly} (hf : GeometricallyIrreducible f) :
    Irreducible (complexifyReal f) :=
  hf.map complexifyEquiv.toMulEquiv

lemma eval_real_map (f : RPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then (z.re : ℂ) else (z.im : ℂ))
      (map Complex.ofRealHom f) =
      (eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f : ℂ) := by
  rw [eval_map]
  have h := eval₂_comp Complex.ofRealHom (fun i : Fin 2 => if i = 0 then z.re else z.im) f
  simpa only [Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite] using h.symm

lemma complexifyReal_locus (f : RPoly) : realLocus (complexifyReal f) = cartesianLocus f := by
  ext z
  change eval _ (complexify (map Complex.ofRealHom f)) = 0 ↔ eval _ f = 0
  rw [eval_complexify, eval_real_map, Complex.ofReal_eq_zero]

/-- Affine parameters `(a, b)` of the direct symmetries `z ↦ a z + b` of the Cartesian locus. -/
abbrev CartesianDirectSymmetries (f : RPoly) :=
  {ab : ℂ × ℂ // DirectSymmetry (cartesianLocus f) ab.1 ab.2}

/-- The direct bound, starting with the paper's real Cartesian polynomial. -/
theorem cartesian_direct_bound {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (CartesianDirectSymmetries f) ∧
      Nat.card (CartesianDirectSymmetries f) ≤ max f.totalDegree (2 * f.totalDegree - 4) := by
  have h := direct_euclidean_bound (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
  simpa only [DirectSymmetries, complexifyReal_locus, complexifyReal_degree] using h

/-- The full bound for the actual Euclidean-isometry subgroup of a Cartesian zero set. -/
theorem cartesian_isometry_bound {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R) :
    Finite (isometrySetGroup (cartesianLocus f)) ∧
      Nat.card (isometrySetGroup (cartesianLocus f)) ≤ 2 * f.totalDegree := by
  have h := isometry_group_bound (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
  simpa only [isometrySymmetryGroup, complexifyReal_locus, complexifyReal_degree] using h

theorem cartesian_extremal_classification {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 5 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    (hcard : Nat.card (CartesianDirectSymmetries f) = 2 * f.totalDegree - 4) :
    ∃ c t α : ℂ, c ≠ 0 ∧ ‖α‖ = 1 ∧ α ≠ star α ∧
      cartesianLocus f = (fun z : ℂ => c * z + t) ''
        realLocus (familyPolynomial (f.totalDegree - 2) α) := by
  have h := extremal_classification (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus])
    (by simpa only [NotCircle, complexifyReal_locus] using hnc)
    (by simpa only [DirectSymmetries, complexifyReal_locus, complexifyReal_degree] using hcard)
  simpa only [complexifyReal_locus, complexifyReal_degree] using h

end CurveSymmetry
