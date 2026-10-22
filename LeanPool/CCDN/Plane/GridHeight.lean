/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Noether.BivariateTotalDegree
public import Mathlib.Basic.Real.Basic
import LeanPool.CCDN.Height.MultivariateGridHeight
import LeanPool.CCDN.Noether.ShearNormalization

/-! A coefficient-height witness on the bounded integer plane grid: the case n = 2 of
`CCDN.Height.MultivariateGridHeight`. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Evaluating the nested-polynomial form of a bivariate polynomial `f` at `(x, y)` (inner
variable at `y`, outer variable at `x`) agrees with evaluating `f` at `![x, y]`. -/
lemma bivariatePolynomialEquiv_eval {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 2) R) (x y : R) :
    (Polynomial.map (Polynomial.evalRingHom y) (bivariatePolynomialEquiv R f)).eval x =
      MvPolynomial.eval ![x, y] f := by
  have he : (Polynomial.evalRingHom x).comp
      ((Polynomial.mapRingHom (Polynomial.evalRingHom y)).comp
        (bivariatePolynomialEquiv R).toRingHom) =
      MvPolynomial.eval ![x, y] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [bivariatePolynomialEquiv_C]
    · intro i
      fin_cases i <;> simp [bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- Natural-number points of `Fin 2 → ℕ`, written as vectors of length two. -/
private lemma natCast_fin_two_eq {R : Type*} [CommRing R] (a : Fin 2 → ℕ) :
    (fun i => (a i : R)) = ![(a 0 : R), (a 1 : R)] := by
  funext i
  fin_cases i <;> rfl

/-- The plane case of `multivariate_coefficient_bound_of_integer_grid`, for nested
polynomials. -/
theorem bivariate_coefficient_bound_of_integer_grid (f : ℝ[X][X]) {d : ℕ}
    (hd : bivariateTotalDegree f ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ x y : ℕ, x ≤ d → y ≤ d →
      |(Polynomial.map (Polynomial.evalRingHom (y : ℝ)) f).eval (x : ℝ)| ≤ H) (i j : ℕ) :
    |(f.coeff i).coeff j| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * H := by
  have h := multivariate_coefficient_bound_of_integer_grid
    ((bivariatePolynomialEquiv ℝ).symm f) hd hH (fun a ha => by
      have hh := heval (a 0) (a 1) (ha 0) (ha 1)
      rwa [← (bivariatePolynomialEquiv ℝ).apply_symm_apply f, bivariatePolynomialEquiv_eval,
        ← natCast_fin_two_eq] at hh) (Finsupp.cons i (Finsupp.single 0 j))
  rwa [← bivariatePolynomialEquiv_coeff, AlgEquiv.apply_symm_apply] at h

/-- A nonzero integer plane polynomial of total degree at most `d` has a nonzero value at some
natural point `(x, y)` with `x, y ≤ d`, and every coefficient is bounded by
`(d + 1) ^ (2 * (d + 1))` times the absolute value of that value. -/
theorem exists_integer_plane_grid_height_witness (f : MvPolynomial (Fin 2) ℤ)
    (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ x y : ℕ, x ≤ d ∧ y ≤ d ∧ MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f ≠ 0 ∧ ∀ m,
      |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) *
        |(MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ)| := by
  obtain ⟨a, ha, hne, hc⟩ := exists_integer_multivariate_grid_height_witness f hf hd
  lift a to Fin 2 → ℕ using fun i => (ha i).1
  rw [natCast_fin_two_eq] at hne hc
  exact ⟨a 0, a 1, Int.ofNat_le.mp (ha 0).2, Int.ofNat_le.mp (ha 1).2, hne, hc⟩

/-- The plane case of `integer_multivariate_coefficient_bound_of_grid`. -/
theorem integer_plane_coefficient_bound_of_grid (f : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hd : f.totalDegree ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ x y : ℕ, x ≤ d → y ≤ d → |(MvPolynomial.eval ![(x : ℤ), (y : ℤ)] f : ℝ)| ≤ H)
    (m : Fin 2 →₀ ℕ) : |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * H :=
  integer_multivariate_coefficient_bound_of_grid f hd hH (fun a ha => by
    rw [natCast_fin_two_eq]; exact heval (a 0) (a 1) (ha 0) (ha 1)) m

end
end CCDN
