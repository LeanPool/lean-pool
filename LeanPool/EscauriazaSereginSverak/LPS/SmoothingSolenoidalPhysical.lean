/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus

/-!
# Classical solenoidality of smooth `J` fields

The `J` condition on a regularized velocity slice gives the pointwise
divergence identity used in its high-order pressure cancellation.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A spatially smooth `J` field is solenoidal at every point
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_smooth_isInJ_solenoidal
    {u : Vec3 → Vec3} (hJ : IsInJ u)
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) :
    ∀ x : Vec3,
      ∑ i : Fin 3, spatialDeriv (fun y => u y i) i x = 0 := by
  have hC1 : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => u x i) := by
    intro i
    exact (hu i).of_le (by norm_num)
  exact CKN.Leray.regUniform_weakDivFree_contDiff_divergence_eq_zero
    hC1 (isInJ_weakDivFree hJ)

end ESS
