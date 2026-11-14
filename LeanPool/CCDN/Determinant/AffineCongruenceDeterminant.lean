/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.PolynomialPredicates
public import LeanPool.CCDN.Algebra.ScaledHomogenization
public import LeanPool.CCDN.Determinant.HypersurfaceDeterminantRank
public import LeanPool.CCDN.Height.CountingHypotheses
import LeanPool.CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import LeanPool.CCDN.Determinant.SmoothCongruenceDeterminant

/-! Congruence-refined determinant estimates for affine zeros and
arbitrary bounded-degree polynomial evaluation columns. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The homogeneous coordinates `(1, x)` of an integer point `x` are primitive: their gcd is `1`. -/
lemma primitive_affine_integer_coordinates {n : ℕ} (x : Fin n → ℤ) :
    Finset.univ.gcd (Fin.cons 1 x) = 1 := by
  have he : insert (0 : Fin (n + 1)) univ = univ := insert_eq_of_mem (mem_univ _)
  have hh := congrArg (fun S : Finset (Fin (n + 1)) => S.gcd (Fin.cons 1 x)) he
  simpa only [Finset.gcd_insert, Fin.cons_zero, gcd_one_left] using hh.symm

/-- Homogenization transfers the proved global-plus-congruence estimate
without changing a single affine evaluation. -/
theorem exists_affine_congruence_determinant_log_lower {n s N M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree)
    (G : Fin N → MvPolynomial (Fin (n + 2)) ℤ) (hG : ∀ j, (G j).totalDegree ≤ M)
    (x : Fin s → IntPoint (n + 2)) (hx : ∀ i, eval (x i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (x i) (G j)).map ((↑) : ℤ → ℚ)).row)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x) :
    ∃ bad : Finset ℕ,
      (∀ p, p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
        HypersurfaceBadReduction (scaledHomogenize f.totalDegree 1 f) p) ∧
      hypersurfaceRankLowerBound n s f.totalDegree (∑ p ∈ bad ∪ P, Real.log p / p) +
        (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) *
          (∑ p ∈ P, Real.log p) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (G j))) := by
  classical
  let F := scaledHomogenize f.totalDegree 1 f
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  have hF : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous 1 f le_rfl
  have hFir : AbsolutelyIrreducible F :=
    (unscaledHomogenize_absolute_irreducible_iff f hf0).mpr hir
  let H := fun j => scaledHomogenize M 1 (G j)
  have hH : ∀ j, (H j).IsHomogeneous M := fun j => scaledHomogenize_homogeneous 1 _ (hG j)
  let z : Fin s → IntPoint (n + 3) := fun i => Fin.cons 1 (x i)
  have hz : ∀ i, eval (z i) F = 0 := by
    intro i
    rw [← affineChart_eval, affineChart_scaledHomogenize_one]
    exact hx i
  have he : (Matrix.of fun i j => eval (z i) (H j)) =
      Matrix.of fun i j => eval (x i) (G j) := by
    ext i j
    change eval (Fin.cons 1 (x i)) (scaledHomogenize M 1 (G j)) = _
    rw [← affineChart_eval, affineChart_scaledHomogenize_one]
    rfl
  have hrows' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (H j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hrows
  have hchart : projectiveHypersurfaceChart (0 : Fin (n + 3)) F = f := by
    simp only [projectiveHypersurfaceChart, projectiveChart, Equiv.swap_self, Equiv.coe_refl,
      rename_id_apply, F, affineChart_scaledHomogenize_one]
  obtain ⟨bad, hbad, hbound⟩ := exists_smooth_congruence_determinant_log_lower hs F hF hd hFir
    ⟨hH, fun i => primitive_affine_integer_coordinates (x i), hz, hrows'⟩ P hres.prime
    (fun _ => 0) a (by simpa only [hchart] using hres.eval_eq_zero)
    (by simpa only [hchart] using hres.smooth)
    (by intro p hp i; exact isCoprime_one_right)
    (by intro p hp i j; simpa only [Equiv.swap_self, Equiv.refl_apply,
        z, Fin.cons_succ, Fin.cons_zero, mul_one] using hres.dvd_sub p hp i j)
  rw [he] at hbound
  exact ⟨bad, hbad, hbound⟩

end
end CCDN
