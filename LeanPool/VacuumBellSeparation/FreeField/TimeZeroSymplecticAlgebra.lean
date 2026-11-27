/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CanonicalSourceHull

/-!
# Bilinearity and disjoint-support locality of the literal source form

All equalities are derived from the actual integral of f g' - g f'. The
locality statement uses disjoint spatial supports and has no covariance or
representation premise.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

theorem timeZeroSymplectic_add_left (u v w : TimeZeroSource) :
    timeZeroSymplectic (u + v) w = timeZeroSymplectic u w + timeZeroSymplectic v w := by
  rw [timeZeroSymplectic, timeZeroSymplectic, timeZeroSymplectic,
    ← integral_add (integrable_timeZeroSymplectic u w) (integrable_timeZeroSymplectic v w)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (u.1.1 x + v.1.1 x) * w.2.1 x - (u.2.1 x + v.2.1 x) * w.1.1 x = _
    ring

theorem timeZeroSymplectic_skew (u v : TimeZeroSource) :
    timeZeroSymplectic u v = -timeZeroSymplectic v u := by
  rw [timeZeroSymplectic, timeZeroSymplectic, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem timeZeroSymplectic_add_right (u v w : TimeZeroSource) :
    timeZeroSymplectic u (v + w) = timeZeroSymplectic u v + timeZeroSymplectic u w := by
  rw [timeZeroSymplectic_skew u (v + w), timeZeroSymplectic_add_left,
    timeZeroSymplectic_skew v u, timeZeroSymplectic_skew w u]
  ring

theorem timeZeroSymplectic_smul_left (a : ℝ) (u v : TimeZeroSource) :
    timeZeroSymplectic (a • u) v = a * timeZeroSymplectic u v := by
  rw [timeZeroSymplectic, timeZeroSymplectic, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (a * u.1.1 x) * v.2.1 x - (a * u.2.1 x) * v.1.1 x = _
    ring

theorem timeZeroSymplectic_zero_left (u : TimeZeroSource) : timeZeroSymplectic 0 u = 0 := by
  change (∫ x : EuclideanSpace ℝ (Fin 3),
    (0 : ℝ) * u.2.1 x - (0 : ℝ) * u.1.1 x) = 0
  simp

theorem timeZeroSymplectic_zero_right (u : TimeZeroSource) : timeZeroSymplectic u 0 = 0 := by
  rw [timeZeroSymplectic_skew, timeZeroSymplectic_zero_left, neg_zero]

/-- Disjoint spatial localization makes the actual symplectic cross form vanish. -/
theorem timeZeroSymplectic_eq_zero_of_disjoint
    {U W : Set (EuclideanSpace ℝ (Fin 3))} (hUW : Disjoint U W)
    {u v : TimeZeroSource} (hu : u ∈ localizedTimeZeroSources U)
    (hv : v ∈ localizedTimeZeroSources W) : timeZeroSymplectic u v = 0 := by
  rw [timeZeroSymplectic]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ U
    · have hxW : x ∉ W := fun h => Set.disjoint_left.mp hUW hx h
      have hv₁ : v.1.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxW (hv.1 h))
      have hv₂ : v.2.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxW (hv.2 h))
      simp only [hv₁, hv₂, mul_zero, sub_zero, Pi.zero_apply]
    · have hu₁ : u.1.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hu.1 h))
      have hu₂ : u.2.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hu.2 h))
      simp only [hu₁, hu₂, zero_mul, sub_zero, Pi.zero_apply]

end VacuumBellSeparation
