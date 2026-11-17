/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Plane.FiniteFieldConstants
public import LeanPool.CCDN.Plane.FiniteFieldZeroPlanes
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Real.Sqrt
import LeanPool.CCDN.Plane.SectionBounds

/-! Sum the sharp good-section bound and the separately controlled bad and
zero contributions over the full plane parameter space. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The exact incidence identity with each section bounded according to its
equation. -/
theorem plane_sections_incidence_bound {σ : Type*} [Fintype σ]
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial σ (ZMod p))
    (hsize : stepanovThreshold (f.totalDegree : ℝ) < p) :
    (Nat.card {z : σ → ZMod p // eval z f = 0} : ℝ) *
        (p : ℝ) ^ (2 * Fintype.card σ + 2) ≤
      (p : ℝ) ^ (3 * Fintype.card σ) *
        (p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) +
      (Nat.card (BadPlaneParameters f) : ℝ) * (f.totalDegree * p) +
      (Nat.card (ZeroPlaneParameters f) : ℝ) * (p : ℝ) ^ 2 := by
  classical
  let V := PlaneParameters σ → ZMod p
  let B : V → Prop := fun v =>
    bivariateTotalDegree (universalPlaneSection f v) ≠ f.totalDegree ∨
      ¬Irreducible (bivariateMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (universalPlaneSection f v))
  let Z : V → Prop := fun v => universalPlaneSection f v = 0
  let A : ℝ := p + planeResidueConstant * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p
  have hA : 0 ≤ A := by
    have := planeResidueConstant_pos
    dsimp [A]
    positivity
  have hpoint (v : V) : (Nat.card (PlaneSectionPoints f v) : ℝ) ≤
      A + (if B v then (f.totalDegree : ℝ) * p else 0) +
        (if Z v then (p : ℝ) ^ 2 else 0) := by
    by_cases hz : Z v
    · have hh : (Nat.card (PlaneSectionPoints f v) : ℝ) ≤ (p : ℝ) ^ 2 := by
        exact_mod_cast (by simpa only [ZMod.card] using planeSectionPoints_card_le_square f v)
      rw [ite_eq_left hz]
      have hb : (0 : ℝ) ≤ if B v then (f.totalDegree : ℝ) * p else 0 := by split_ifs <;> positivity
      linarith
    · rw [ite_eq_right hz, add_zero]
      by_cases hb : B v
      · rw [ite_eq_left hb]
        have hh : (Nat.card (PlaneSectionPoints f v) : ℝ) ≤ (f.totalDegree : ℝ) * p := by
          exact_mod_cast (by simpa only [ZMod.card] using
            planeSectionPoints_card_le_degree_mul_card f v hz)
        linarith
      · rw [ite_eq_right hb, add_zero]
        apply planeSectionPoints_card_le_add_mul_sqrt p f v _ hsize
        exact not_not.mp (fun hh => hb (Or.inr hh))
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hpoint v)
  have hi : (Nat.card {z : σ → ZMod p // eval z f = 0} : ℝ) *
      (p : ℝ) ^ (2 * Fintype.card σ + 2) =
      ∑ v : V, (Nat.card (PlaneSectionPoints f v) : ℝ) := by
    have hh := sum_planeSectionPoints_card f
    rw [ZMod.card] at hh
    exact_mod_cast hh.symm
  have hB : (∑ v : V, if B v then (f.totalDegree : ℝ) * p else 0) =
      (Nat.card (BadPlaneParameters f) : ℝ) * ((f.totalDegree : ℝ) * p) := by
    rw [← Finset.sum_filter B (fun _ : V => (f.totalDegree : ℝ) * p)]
    simp [V, B, BadPlaneParameters, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hZ : (∑ v : V, if Z v then (p : ℝ) ^ 2 else 0) =
      (Nat.card (ZeroPlaneParameters f) : ℝ) * (p : ℝ) ^ 2 := by
    rw [← Finset.sum_filter Z (fun _ : V => (p : ℝ) ^ 2)]
    simp [V, Z, ZeroPlaneParameters, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_add_distrib, hB, hZ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [hi]
  convert hsum using 1
  simp [A, V, PlaneParameters, Nat.mul_comm]

end
end CCDN
