/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.AuxiliaryPolynomial.AffineCongruenceHeight
public import LeanPool.CCDN.ForMathlib.StandardExponents
import LeanPool.CCDN.AuxiliaryPolynomial.StandardMonomialAuxiliary
import LeanPool.CCDN.AuxiliaryPolynomial.WeightedMonomialDeterminant

/-! Auxiliary polynomials from the competing congruence determinant
lower bound and weighted archimedean upper bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

private theorem square_minorGcd_eq_abs_det {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) :
    Int.Matrix.minorGcd A = |A.det| := by
  classical
  let : Nonempty (Set.powersetCard (Fin s) s) :=
    ⟨⟨univ, by simp⟩⟩
  rw [minorGcd_eq_gcd_plucker]
  have hp : exteriorPower.plucker s A.row = fun _ => A.det :=
    funext (fun S => exteriorPower.plucker_fin_eq_det A.row S)
  rw [hp]
  rw [Finset.gcd_eq_gcd_image, Finset.image_const univ_nonempty]
  simp only [Finset.gcd_singleton, id_eq, ← Int.abs_eq_normalize]

/-- The lower bound for the logarithm of a nonzero `s × s` determinant of monomials evaluated
at integral zeros of an absolutely irreducible affine equation of degree `d` in `n + 2`
variables with coefficient height at most `H`, when the zeros lie in smooth residue classes
modulo primes whose logarithms sum to `Q`. -/
def affineCongruenceDeterminantLower (n d s : ℕ) (H Q : ℝ) : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
      (Real.log s - (n + 1 : ℝ) * (4 * Real.log d +
        congruenceHeightCharge (n + 3) d H Q) - hypersurfaceDeterminantError n) +
    (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) * Q

/-- A strict numerical gap forces every maximal determinant to vanish.
The arithmetic divisibility and archimedean bounds come from the
equation, its smooth residue classes, and the integer points. -/
private theorem affine_congruence_evaluation_det_eq_zero {n s M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (mon : Fin s → (Fin (n + 2) →₀ ℕ))
    (hdegree : ∀ j, Finsupp.degree (mon j) ≤ M)
    {B : ℝ} {x : Fin s → IntPoint (n + 2)} (hxB : IsBoxZeroFamily f B x)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x)
    (hgap : Real.log (s.factorial : ℝ) +
      (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
      affineCongruenceDeterminantLower n f.totalDegree s H (∑ p ∈ P, Real.log p)) :
    (evaluationMatrix mon x).det = 0 := by
  by_contra hne
  let G : Fin s → MvPolynomial (Fin (n + 2)) ℤ :=
    fun j => monomial (mon j) 1
  have hG : ∀ j, (G j).totalDegree ≤ M := fun j =>
    (totalDegree_monomial_le _ _).trans (hdegree j)
  have hmat : (Matrix.of fun i j => eval (x i) (G j)) = evaluationMatrix mon x := by
    ext i j
    simp only [Matrix.of_apply, G, eval_monomial, one_mul]
    rfl
  have hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (x i) (G j)).map ((↑) : ℤ → ℚ)).row := by
    rw [hmat]
    apply Matrix.linearIndependent_rows_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    change ((Int.castRingHom ℚ).mapMatrix (evaluationMatrix mon x)).det ≠ 0
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    change ((evaluationMatrix mon x).det : ℚ) ≠ 0
    exact_mod_cast hne
  have hlo := affine_congruence_determinant_log_lower_height hs f hir hd H hH hcoeff
    G hG x hxB.eval_eq_zero hrows P a hres
  rw [hmat, square_minorGcd_eq_abs_det, Int.cast_abs] at hlo
  have hhi := weighted_evaluation_det_log_bound mon x hxB.one_le_radius hxB.abs_le hne
  exact (not_lt_of_ge (hlo.trans hhi)) hgap

/-- The determinant gap yields an integer auxiliary, proper over
the rationals, for every given finite family of points in the residue classes. -/
theorem exists_affine_congruence_auxiliary_of_gap {n N t M : ℕ} (hN : 0 < N)
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H)
    (mon : Fin N → (Fin (n + 2) →₀ ℕ)) (hmon : Function.Injective mon)
    (hstd : ∀ j, mon j ∈ Ideal.standardExponents
      (Ideal.span {map (Int.castRingHom ℚ) f}) MonomialOrder.degLex)
    (hdegree : ∀ j, Finsupp.degree (mon j) ≤ M)
    {B : ℝ} {x : Fin t → IntPoint (n + 2)} (hxB : IsBoxZeroFamily f B x)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x)
    (hgap : Real.log (N.factorial : ℝ) +
      (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
      affineCongruenceDeterminantLower n f.totalDegree N H (∑ p ∈ P, Real.log p)) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      g.totalDegree ≤ M ∧ ∀ i, eval (x i) g = 0 := by
  apply exists_standard_auxiliary_of_zero_determinants
    (map (Int.castRingHom ℚ) f) mon hmon hstd hdegree x
  intro b
  exact affine_congruence_evaluation_det_eq_zero hN f hir hd H hH hcoeff mon hdegree (x := x ∘ b)
    ⟨hxB.one_le_radius, fun i => hxB.eval_eq_zero (b i), fun i j => hxB.abs_le (b i) j⟩ P a
    ⟨hres.prime, hres.eval_eq_zero, hres.smooth, fun p hp i j => hres.dvd_sub p hp (b i) j⟩ hgap

end
end CCDN
