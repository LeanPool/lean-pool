/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Analysis.Complex.Norm
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Height.ComplexGridInterpolation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-! Coefficient control on the integer grid in every finite dimension.
Iterating the sharp univariate bound gives the factor 3^(nd) over ℂ (CCDN Lemma 3.4.2);
the real and integer statements, with the weaker factor (d+1)^(n(d+1)), are corollaries
obtained by embedding the coefficients in ℂ. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Iterated one-variable interpolation controls every coefficient of a complex polynomial
from its values on the full grid {0,...,d}^n, with the exact factor 3^(nd). -/
private theorem complex_multivariate_coefficient_bound_of_integer_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → ‖eval (fun i => (a i : ℂ)) f‖ ≤ H)
    (m : Fin n →₀ ℕ) :
    ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) * H := by
  induction n generalizing H with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    have hh := heval (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rw [eq_C_of_isEmpty f] at hh
    simpa [hm] using hh
  | succ n ih =>
    let g := (finSuccEquiv ℂ n f).coeff (m 0)
    have hg : g.totalDegree ≤ d := by
      by_cases hzero : g = 0
      · simp [hzero]
      · have hh := totalDegree_coeff_finSuccEquiv_add_le f (m 0) hzero
        dsimp only [g]
        omega
    have hvalues (a : Fin n → ℕ) (ha : ∀ i, a i ≤ d) :
        ‖eval (fun i => (a i : ℂ)) g‖ ≤ (3 : ℝ) ^ d * H := by
      have hh := complex_polynomial_coefficient_bound_of_integer_grid
        (Polynomial.map (eval (fun i => (a i : ℂ))) (finSuccEquiv ℂ n f))
        (Polynomial.natDegree_map_le.trans ((natDegree_finSuccEquiv f).le.trans
          ((degreeOf_le_totalDegree f 0).trans hd))) hH
        (fun x hx => ?_) (m 0)
      · simpa only [g, Polynomial.coeff_map] using hh
      · rw [← eval_eq_eval_mv_eval']
        have hcons : (Fin.cons (x : ℂ) (fun i => (a i : ℂ))) =
            (fun i => (((Fin.cons x a : Fin (n + 1) → ℕ) i) : ℂ)) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [hcons]
        exact heval (Fin.cons x a) (fun i => Fin.cases hx ha i)
    have hh := ih g hg (show 0 ≤ (3 : ℝ) ^ d * H by positivity) hvalues m.tail
    rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] at hh
    convert hh using 1
    rw [show (n + 1) * d = n * d + d by ring, pow_add]
    ring

/-- A complex polynomial of total degree at most `d` has a grid point `a ∈ [0, d]ⁿ` at which
its value bounds every coefficient: `‖coeff m‖ ≤ 3^(n d) ‖f(a)‖`. -/
theorem exists_complex_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℂ) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℕ, (∀ i, a i ≤ d) ∧ ∀ m,
      ‖f.coeff m‖ ≤ (3 : ℝ) ^ (n * d) * ‖eval (fun i => (a i : ℂ)) f‖ := by
  classical
  let S := Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))
  have hS : S.Nonempty := ⟨fun _ => 0, by simp [S]⟩
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image
    (fun a => ‖eval (fun i => (a i : ℂ)) f‖) hS
  have hb : ∀ i, a i ≤ d := by
    simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using ha
  refine ⟨a, hb, complex_multivariate_coefficient_bound_of_integer_grid f hd (norm_nonneg _) ?_⟩
  intro b hb
  exact hmax b (by simpa only [S, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] using hb)

/-- The sharp factor 3^(nd) is at most the factor (d+1)^(n(d+1)) of the real statements. -/
private lemma three_pow_mul_le (n d : ℕ) :
    (3 : ℝ) ^ (n * d) ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) := by
  rw [pow_mul', pow_mul']
  gcongr
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d <;> norm_num
  · have h3 : (3 : ℝ) ≤ d + 1 := by exact_mod_cast (show 3 ≤ d + 1 by omega)
    calc (3 : ℝ) ^ d ≤ ((d : ℝ) + 1) ^ d := by gcongr
      _ ≤ ((d : ℝ) + 1) ^ (d + 1) := pow_le_pow_right₀ (by linarith) d.le_succ

/-- Transfer of the complex grid bound along a ring homomorphism into ℂ. -/
private lemma coefficient_bound_of_integer_grid_of_ringHom {R : Type*} [CommRing R]
    (φ : R →+* ℂ) {n : ℕ} (f : MvPolynomial (Fin n) R) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → ‖φ (eval (fun i => (a i : R)) f)‖ ≤ H)
    (m : Fin n →₀ ℕ) :
    ‖φ (f.coeff m)‖ ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  have h := complex_multivariate_coefficient_bound_of_integer_grid (map φ f)
    ((totalDegree_map_le _ _).trans hd) hH
    (fun a ha => by simpa [map_eval, Function.comp_def] using heval a ha) m
  rw [coeff_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (three_pow_mul_le n d) hH)

/-- Iterated one-variable interpolation controls every coefficient from the
values on the full grid, with a constant depending only on degree and dimension. -/
theorem multivariate_coefficient_bound_of_integer_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℝ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) → |eval (fun i => (a i : ℝ)) f| ≤ H)
    (m : Fin n →₀ ℕ) :
    |f.coeff m| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  simpa [Complex.norm_real] using coefficient_bound_of_integer_grid_of_ringHom
    Complex.ofRealHom f hd hH (fun a ha => by simpa [Complex.norm_real] using heval a ha) m

/-- If an integer polynomial of total degree at most `d` has values of absolute value at most
`H` on the grid `{0, …, d}ⁿ`, then every coefficient has absolute value at most
`(d + 1) ^ (n * (d + 1)) * H`. -/
theorem integer_multivariate_coefficient_bound_of_grid {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) {d : ℕ} (hd : f.totalDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ a : Fin n → ℕ, (∀ i, a i ≤ d) →
      |(eval (fun i => (a i : ℤ)) f : ℝ)| ≤ H) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * H := by
  simpa [Complex.norm_intCast] using coefficient_bound_of_integer_grid_of_ringHom
    (Int.castRingHom ℂ) f hd hH
    (fun a ha => by simpa [Complex.norm_intCast] using heval a ha) m

/-- A nonzero integer polynomial of total degree at most `d` has a point `a` of the grid
`{0, …, d}ⁿ` with `f(a) ≠ 0` such that every coefficient has absolute value at most
`(d + 1) ^ (n * (d + 1)) * |f(a)|`. -/
theorem exists_integer_multivariate_grid_height_witness {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf : f ≠ 0) {d : ℕ} (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧ eval a f ≠ 0 ∧ ∀ m,
      |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) * |(eval a f : ℝ)| := by
  obtain ⟨a, ha, hc⟩ := exists_complex_multivariate_grid_height_witness
    (map (Int.castRingHom ℂ) f) ((totalDegree_map_le _ _).trans hd)
  have he : eval (fun i => (a i : ℂ)) (map (Int.castRingHom ℂ) f) =
      ((eval (fun i => (a i : ℤ)) f : ℤ) : ℂ) := by
    simpa [Function.comp_def] using (map_eval (Int.castRingHom ℂ) (fun i => (a i : ℤ)) f).symm
  have hb (m) : |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (n * (d + 1)) *
      |(eval (fun i => (a i : ℤ)) f : ℝ)| := by
    have h := (hc m).trans (mul_le_mul_of_nonneg_right (three_pow_mul_le n d) (norm_nonneg _))
    rwa [coeff_map, he, eq_intCast, Complex.norm_intCast, Complex.norm_intCast] at h
  refine ⟨fun i => (a i : ℤ), fun i => ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr (ha i)⟩, ?_, hb⟩
  intro hz
  refine hf (MvPolynomial.ext _ _ fun m => ?_)
  have hh := hb m
  rw [hz, Int.cast_zero, abs_zero, mul_zero] at hh
  exact_mod_cast abs_nonpos_iff.mp hh

end
end CCDN
