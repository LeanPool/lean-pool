/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingHeatPairing

/-!
# Whole-space pressure cancellation

The pressure gradient has zero energy pairing with a smooth
divergence-free field. This is the scalar integration-by-parts step
in `eq:lps-regularized-Hm-identity`.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The pressure term vanishes when its energy test field is solenoidal
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_solenoidal_pressure_pairing_zero
    {h : Vec3 → Vec3} {p : Vec3 → ℝ}
    (hh : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => h x i))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hh0 : ∀ i : Fin 3, MemLp (fun x => h x i) 2 volume)
    (hh1 : ∀ i : Fin 3, MemLp (spatialDeriv (fun x => h x i) i) 2 volume)
    (hp0 : MemLp p 2 volume)
    (hp1 : ∀ i : Fin 3, MemLp (spatialDeriv p i) 2 volume)
    (hdiv : ∀ x : Vec3,
      ∑ i : Fin 3, spatialDeriv (fun y => h y i) i x = 0) :
    (∑ i : Fin 3,
      ∫ x : Vec3, h x i * spatialDeriv p i x) = 0 := by
  calc
    (∑ i : Fin 3,
      ∫ x : Vec3, h x i * spatialDeriv p i x) =
        ∑ i : Fin 3,
          -(∫ x : Vec3, spatialDeriv (fun y => h y i) i x * p x) := by
            apply Finset.sum_congr rfl
            intro i _
            exact lps_divergence_pairing_direction (hh i) hp i
              (hh0 i) (hh1 i) hp0 (hp1 i)
    _ = -(∫ x : Vec3,
          (∑ i : Fin 3, spatialDeriv (fun y => h y i) i x) * p x) := by
            rw [Finset.sum_neg_distrib]
            congr 1
            rw [← integral_finsetSum]
            · congr 1
              funext x
              rw [Finset.sum_mul]
            · intro i _
              exact (hh1 i).integrable_mul hp0
    _ = 0 := by simp [hdiv]

end ESS
