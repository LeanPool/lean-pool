/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Statements
import LeanPool.CCDN.Curve.AffineCurveCount
import LeanPool.CCDN.Surface.AuxiliaryExponent

/-! Counting the nonlinear components of a surface section using their
total Hilbert degree and the affine curve counting theorem. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The number of integral points of height at most `B` on a finite union of sets is at most
the sum of the numbers of such points on the individual sets. -/
theorem count_biUnion_finset_le {n : ℕ} {ι : Type*}
    (s : Finset ι) (X : ι → Set (RatPoint n)) (B : ℝ) :
    count (⋃ i ∈ s, X i) B ≤ ∑ i ∈ s, count (X i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert i s hi ih =>
    simpa only [Finset.set_biUnion_insert, Finset.sum_insert hi] using
      (count_union_le (X i) (⋃ j ∈ s, X j) B).trans (Nat.add_le_add_left ih _)

/-- The curve counting constant is chosen before the finite family and its
degree budget. This is the nonlinear-component part of the corrected surface
estimate for degrees at least sixteen. -/
theorem nonlinear_curve_union_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (s : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (d : ℕ),
      16 ≤ d → ∀ C B : ℝ, 0 ≤ C → 1 ≤ B →
      (∀ P ∈ s, P.IsPrime ∧ 2 ≤ δ P ∧ HasAffineCurveDegree P (δ P)) →
      (∑ P ∈ s, (δ P : ℝ)) ≤ C * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d) →
      (count (⋃ P ∈ s, idealZeroLocus P) B : ℝ) ≤
        K * Real.exp 1 * (480 * C + 2 * C ^ 4) * (d : ℝ) ^ 18 * B := by
  obtain ⟨K, hK, hcount⟩ := affine_curve_count 3 (by omega)
  refine ⟨K, hK, ?_⟩
  intro s δ d hd C B hC hB hcurve hdegree
  calc
    _ ≤ ∑ P ∈ s, (count (idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_biUnion_finset_le s idealZeroLocus B
    _ ≤ ∑ P ∈ s, K * curveBound (δ P) B := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hp, hδ, hdeg⟩ := hcurve P hP
      exact hcount P hp (δ P) (by omega) hdeg B hB
    _ = K * ∑ P ∈ s, curveBound (δ P) B := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (Real.exp 1 * (480 * C + 2 * C ^ 4) * (d : ℝ) ^ 18 * B) :=
      mul_le_mul_of_nonneg_left
        (sum_curveBound_le_surface_degree_budget s δ hd hC hB (fun P hP => (hcurve P hP).2.1)
          hdegree) hK.le
    _ = _ := by ring

end
end CCDN
