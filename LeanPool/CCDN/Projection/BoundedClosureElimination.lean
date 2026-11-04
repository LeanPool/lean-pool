/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.IntegerLinearForms
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
public import LeanPool.CCDN.Projection.ProjectiveClosureProjection
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import LeanPool.CCDN.Projection.FixedCoordinateElimination
import LeanPool.CCDN.Projection.HilbertLowDegreeEquation
import LeanPool.CCDN.Projection.IntegralProjectionHilbert
import LeanPool.CCDN.Projection.ProjectiveClosureSpecialization

/-! A bounded elimination step whose affine projection and projective
closure projection are both integral. The latter map fixes X₀. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- One step of bounded linear elimination: for a prime ideal `I` in `n + 1` variables of projective
dimension `m < n` and degree `d`, there are integer linear forms in `n` coordinates with
coefficients of absolute value at most `d + 1` whose projection is integral, with prime kernel of
projective dimension `m` and some degree `e` with `0 < e ≤ d`, and such that the associated
projection of the projective closure of `I` is integral as well. -/
theorem exists_fin_integer_closure_elimination_step {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime] (d : ℕ)
    (hdimdeg : HasProjectiveDimensionDegree I m d) (hcodim : m < n) :
    ∃ (c : Fin n → Fin (n + 1) → ℤ) (e : ℕ),
      (∀ i j, |c i j| ≤ d + 1) ∧ 0 < e ∧ e ≤ d ∧
      let a := fun i => integerLinearForm (c i)
      let ψ := projectionCoordinateMap I a
      ψ.IsIntegral ∧ (RingHom.ker ψ).IsPrime ∧
      HasProjectiveDimensionDegree (RingHom.ker ψ) m e ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a)).IsIntegral := by
  obtain ⟨f, hf, hfi, hfd⟩ := exists_mem_ideal_degree_le_multiplicity I d hdimdeg
    (by simpa only [Fintype.card_fin] using Nat.add_lt_add_right hcodim 1)
  let F := renameEquiv ℚ (finSuccEquiv n) f
  have hF : F ≠ 0 := by
    intro h
    apply hf
    exact (renameEquiv ℚ (finSuccEquiv n)).injective (h.trans (map_zero _).symm)
  have hFdeg : F.totalDegree = f.totalDegree := totalDegree_renameEquiv (finSuccEquiv n) f
  obtain ⟨b, hbound, hb, hdir⟩ := exists_bounded_full_degree_direction F hF
  have hbQ : (b none : ℚ) ≠ 0 := by exact_mod_cast hb
  have hdir' : eval (Fin.cons (b none : ℚ) (fun i => (b (some i) : ℚ)))
      (homogeneousComponent f.totalDegree f) ≠ 0 := by
    rw [hFdeg] at hdir
    change eval (fun i => (b i : ℚ))
      (homogeneousComponent f.totalDegree (rename (finSuccEquiv n) f)) ≠ 0 at hdir
    rw [← rename_homogeneousComponent, eval_rename] at hdir
    convert hdir using 1
    congr 1
    congr 1
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  have hcone := fixedCoordinateElimination_isIntegral I f hf hfi b hbQ hdir'
  let c := finEliminationMatrix b
  have hc : ∀ i j, |c i j| ≤ d + 1 := by
    apply finEliminationMatrix_height
    intro i
    refine ⟨(hbound i).1, ?_⟩
    rw [hFdeg] at hbound
    exact (hbound i).2.trans (by exact_mod_cast Nat.add_le_add_right hfd 1)
  have hint := affine_projection_integral_of_closure_integral I
    (fun i => integerLinearForm (c i)) hcone
  obtain ⟨e, he, hed, hker⟩ := integral_linear_projection_dimension_degree I
    (fun i => integerLinearForm (c i)) (fun i => linearForm_totalDegree_le _) hint hdimdeg
  exact ⟨c, e, hc, he, hed, hint, RingHom.ker_isPrime _, hker, hcone⟩

end
end CCDN
