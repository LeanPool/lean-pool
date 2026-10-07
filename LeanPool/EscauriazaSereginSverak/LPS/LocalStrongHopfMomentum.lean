/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopfShift
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularityCore

/-!
# The translated solenoidal weak equation

A strong solution on `[t₀, T]`, translated in time to `[0, T - t₀]`, satisfies
the pressure-free weak momentum equation against solenoidal tests
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- The translated strong solution satisfies the weak momentum equation
against every smooth compactly supported solenoidal test field. -/
theorem lps_shift_momentum {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 (T - t₀)) →
      (∀ z : ParabolicPoint,
        ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 (T - t₀)),
        (-(∑ i : Fin 3, u (lpsShift t₀ z) i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u (lpsShift t₀ z) i * u (lpsShift t₀ z) j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du (lpsShift t₀ z) i j * spatialPartial (fun y => φ y i) j z) = 0 := by
  intro φ hφ hdiv
  have h0 : t₀ + 0 = t₀ := add_zero t₀
  have hT : t₀ + (T - t₀) = T := by ring
  have hφ₀ := lps_shift_testFunction t₀ hφ
  rw [h0, hT] at hφ₀
  have hinv : ∀ z : ParabolicPoint, lpsShift t₀ ((z.1, z.2 - t₀) : ParabolicPoint) = z := by
    intro z
    exact Prod.ext rfl (by simp [lpsShift])
  have hdiv₀ : ∀ z : ParabolicPoint,
      ∑ i : Fin 3, spatialPartial (fun y => (fun y : Vec3 × ℝ => φ (y.1, y.2 - t₀)) y i) i z = 0
        := by
    intro z
    have := hdiv (z.1, z.2 - t₀)
    have e : ∀ i : Fin 3, spatialPartial (fun y => (fun y : Vec3 × ℝ => φ (y.1, y.2 - t₀)) y i)
      i z =
        spatialPartial (fun y => φ y i) i (z.1, z.2 - t₀) := by
      intro i
      have h := lps_shift_spatialPartial t₀ (fun y => φ y i) i (z.1, z.2 - t₀)
      rw [hinv z] at h
      exact h
    simp only [e]
    exact this
  have heq := lps_strong_solution_weak_equation_of_divFree_test hU _ hφ₀ hdiv₀
  have hmp := lps_shift_measurePreserving t₀ 0 (T - t₀)
  rw [h0, hT] at hmp
  rw [← hmp.integral_comp (lps_shift_measurableEmbedding t₀)] at heq
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun z => ?_)) heq
  have e1 : ∀ i : Fin 3, timePartial (fun y : ParabolicPoint => φ (y.1, y.2 - t₀) i)
      (lpsShift t₀ z) = timePartial (fun y => φ y i) z := fun i =>
    lps_shift_timePartial t₀ (fun y => φ y i) z
  have e2 : ∀ i j : Fin 3, spatialPartial (fun y : ParabolicPoint => φ (y.1, y.2 - t₀) i) j
      (lpsShift t₀ z) = spatialPartial (fun y => φ y i) j z := fun i j =>
    lps_shift_spatialPartial t₀ (fun y => φ y i) j z
  simp only [e1, e2]

end ESS.LPS

end
