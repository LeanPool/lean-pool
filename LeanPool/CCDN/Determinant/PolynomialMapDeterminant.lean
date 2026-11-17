/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.HomogeneousMonomials
public import LeanPool.CCDN.Determinant.HeightDeterminant
public import LeanPool.CCDN.Height.CountingHypotheses
import LeanPool.CCDN.Algebra.HomogeneousRankDichotomy
import LeanPool.CCDN.Determinant.HomogeneousDeterminantComparison

/-! The determinant comparison for polynomial homogeneous-coordinate maps of
integer plane-curve points. The residue geometry comes from the plane
equation, so coordinates such as (H,x,y) need no rational rows. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix Real

/-- Evaluating the composite `g ∘ τ` of a polynomial map `τ` and a polynomial `g` at `z` is
evaluating `g` at `τ(z)`. -/
lemma eval_polynomial_coordinate_map {R : Type*} [CommRing R] {n m : ℕ}
    (τ : Fin m → MvPolynomial (Fin n) R) (g : MvPolynomial (Fin m) R) (z : Fin n → R) :
    eval z (aeval τ g) = eval (fun j => eval z (τ j)) g := by
  change eval z (eval₂ C τ g) = _
  rw [← eval_assoc]
  rfl

private lemma polynomial_coordinate_evaluation_matrix {M s : ℕ}
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ) (z : Fin s → Fin 2 → ℤ) :
    (Matrix.of fun i k => eval (z i) (aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ)))) =
      evaluationMatrix (homogeneousMonomials 2 M) (fun i j => eval (z i) (τ j)) := by
  ext i k
  change eval (z i) (aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ))) =
    (homogeneousMonomials 2 M k).prod (fun j e => eval (z i) (τ j) ^ e)
  have h := eval_polynomial_coordinate_map τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ)) (z i)
  simpa only [eval_monomial, one_mul] using h

/-- The complete comparison on the image of any polynomial coordinate map.
The sharp finite-field count is an explicit hypothesis. -/
theorem polynomial_map_no_auxiliary_height_comparison
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    {q : MvPolynomial (Fin 2) ℤ} {H : ℝ} (hq : IsBoundedPlaneCurve F q d H)
    (τ : Fin 3 → MvPolynomial (Fin 2) ℤ) (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, eval (z i) q = 0)
    {B C : ℝ} (himage : IsBoxZeroFamily f B (fun i j => eval (z i) (τ j))) (hC : 0 ≤ C)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (fun j => eval (z i) (τ j)) g = 0) → f ∣ g)
    (hcount : PlaneResidueCountBound C d q) :
    ∃ s : ℕ, 0 < s ∧ s + (2 + (M - d)).choose (M - d) = (2 + M).choose M ∧
      2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) - heightDeterminantError C) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM
      (fun i j => eval (z i) (τ j)) himage.eval_eq_zero himage.one_le_radius himage.abs_le hrel
  have hs := (plane_homogeneous_rank_bounds hd hdM hr).1
  refine ⟨s, hs, hr, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let g := fun k => aeval τ (monomial (homogeneousMonomials 2 M k) (1 : ℤ))
  have he := polynomial_coordinate_evaluation_matrix (M := M) τ (z ∘ a)
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i k => eval ((z ∘ a) i) (g k)).map ((↑) : ℤ → ℚ)).row := by
    rw [show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he]
    exact hi
  have hqdegree := hq.totalDegree_eq
  have hqpos : 0 < q.totalDegree := by simpa only [hqdegree] using hd
  have hcount' := hcount
  rw [← hqdegree] at hcount'
  have hlower := singular_determinant_log_lower_height hs q hqpos hq.irreducible H
    hq.one_le_height hq.coeff_le g (z ∘ a) (fun i => hz (a i)) hi' hC hcount'
  rw [hqdegree, show (Matrix.of fun i k => eval ((z ∘ a) i) (g k)) = _ from he] at hlower
  exact hlower.trans hupper

end
end CCDN
