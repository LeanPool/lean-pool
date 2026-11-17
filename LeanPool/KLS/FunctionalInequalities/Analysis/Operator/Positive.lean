/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Strictly positive operators and their inverses

Generic facts about a continuous linear operator `T` on a real inner product space with
`⟪T v, v⟫ > 0` for `v ≠ 0`: it is a unit in finite dimension, has a two-sided inverse, any right
inverse
of a self-adjoint positive `T` is self-adjoint and strictly positive, and any right inverse of a
unit is
the canonical `Ring.inverse`. Used for the covariance of the BKL localization posterior.
-/

@[expose] public section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/--
A strictly positive operator (`⟪T v, v⟫ > 0` for `v ≠ 0`) on a finite-dimensional space is a unit.
-/
theorem isUnit_of_inner_self_pos (T : E →L[ℝ] E) (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫) :
    IsUnit T := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot T.toLinearMap).mpr
  apply bot_unique
  intro v hv
  have hv' : T v = 0 := hv
  change v = 0
  by_contra hne
  have hp := hpos v hne
  rw [hv', inner_zero_left] at hp
  exact (lt_irrefl 0) hp

/-- A strictly positive operator has a two-sided inverse. -/
theorem exists_inverse_of_inner_self_pos (T : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫) :
    ∃ B : E →L[ℝ] E,
      T.comp B = ContinuousLinearMap.id ℝ E ∧ B.comp T = ContinuousLinearMap.id ℝ E := by
  obtain ⟨u, hu⟩ := isUnit_of_inner_self_pos T hpos
  change ∃ B : E →L[ℝ] E, T * B = 1 ∧ B * T = 1
  refine ⟨↑u⁻¹, ?_, ?_⟩ <;> rw [← hu] <;> simp


end FiniteDimensional

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A right inverse of a self-adjoint operator is self-adjoint. -/
theorem isSelfAdjoint_of_comp_eq_id [CompleteSpace E] (T B : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hTB : T.comp B = ContinuousLinearMap.id ℝ E) : IsSelfAdjoint B := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hf (z : E) : T (B z) = z := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : E →L[ℝ] E => L z) hTB
  have hh := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) (B x) (B y)
  change ⟪T (B x), B y⟫ = ⟪B x, T (B y)⟫ at hh
  rw [hf, hf] at hh
  exact hh.symm

/-- A right inverse of a strictly positive operator is strictly positive. -/
theorem inner_self_pos_of_comp_eq_id (T B : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫)
    (hTB : T.comp B = ContinuousLinearMap.id ℝ E) {v : E} (hv : v ≠ 0) :
    0 < ⟪B v, v⟫ := by
  have hf (z : E) : T (B z) = z := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : E →L[ℝ] E => L z) hTB
  have hBv : B v ≠ 0 := by
    intro hh
    have hz := hf v
    rw [hh, map_zero] at hz
    exact hv hz.symm
  have hp := hpos (B v) hBv
  rw [hf] at hp
  rwa [real_inner_comm] at hp

/-- Any right inverse of a unit equals the canonical `Ring.inverse`. -/
theorem eq_ringInverse_of_comp_eq_id (A B : E →L[ℝ] E) (hu : IsUnit A)
    (hAB : A.comp B = ContinuousLinearMap.id ℝ E) : B = Ring.inverse A := by
  change A * B = 1 at hAB
  calc
    B = (Ring.inverse A * A) * B := by rw [Ring.inverse_mul_cancel A hu, one_mul]
    _ = Ring.inverse A * (A * B) := mul_assoc _ _ _
    _ = Ring.inverse A := by rw [hAB, mul_one]

end General

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Filter Topology
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A positive square root is at least as close to `1` as its square: `‖S - 1‖ ≤ ‖S² - 1‖`. -/
theorem norm_sub_one_le_of_isPositive_mul_self
    {S Q : E →L[ℝ] E} (hS : S.IsPositive)
    (hQ : S * S = Q) : ‖S - 1‖ ≤ ‖Q - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y := (S - 1) x with hy
  have hkey : ‖y‖ ≤ ‖(S + 1) y‖ := by
    have h1 : ‖y‖ * ‖y‖ ≤ ‖(S + 1) y‖ * ‖y‖ := by
      calc
        ‖y‖ * ‖y‖ = ⟪y, y⟫ := (real_inner_self_eq_norm_mul_norm y).symm
        _ ≤ ⟪S y, y⟫ + ⟪y, y⟫ := by
          have := hS.inner_nonneg_left y
          linarith
        _ = ⟪(S + 1) y, y⟫ := by
          rw [add_apply, one_apply_eq_self, inner_add_left]
        _ ≤ ‖(S + 1) y‖ * ‖y‖ := real_inner_le_norm _ _
    rcases (norm_nonneg y).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right h1 h0
  have h2 : (S + 1) y = (Q - 1) x := by
    rw [hy, ← hQ]
    simp only [add_apply, sub_apply,
      one_apply_eq_self, mul_apply_eq_comp, map_sub]
    abel
  calc
    ‖(S - 1) x‖ = ‖y‖ := rfl
    _ ≤ ‖(S + 1) y‖ := hkey
    _ = ‖(Q - 1) x‖ := by rw [h2]
    _ ≤ ‖Q - 1‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _


end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Filter Topology
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An operator with `‖A - 1‖ < 1` has a strictly positive quadratic form on nonzero vectors. -/
theorem inner_self_pos_of_norm_sub_one_lt
    {A : E →L[ℝ] E} (hA : ‖A - 1‖ < 1) {v : E} (hv : v ≠ 0) :
    0 < ⟪A v, v⟫ := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : ⟪A v, v⟫ = ‖v‖ * ‖v‖ + ⟪(A - 1) v, v⟫ := by
    rw [sub_apply, one_apply_eq_self, inner_sub_left,
      real_inner_self_eq_norm_mul_norm]
    ring
  have h2 : ⟪(A - 1) v, v⟫ ≥ -(‖A - 1‖ * ‖v‖ * ‖v‖) := by
    have := real_inner_le_norm ((A - 1) v) (-v)
    rw [inner_neg_right, norm_neg] at this
    have h3 := ContinuousLinearMap.le_opNorm (A - 1) v
    nlinarith [norm_nonneg ((A - 1) v)]
  rw [h1]
  nlinarith [mul_pos hv' hv', norm_nonneg (A - 1)]


end FunctionalInequalities.Analysis
