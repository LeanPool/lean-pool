/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCellNormalized
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianTimeShift

/-!
# Shifted dyadic cells

The short-time grid is translated to the half-space Carleman time
coordinate, which begins at one half.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Forward translation by one half in normalized time. -/
theorem bu_short_time_shift_point_eval (q : ParabolicPoint) :
    buGaussianTimeShiftPoint (1 / 2 : ℝ) q =
      (q.1, 1 / 2 + q.2) := by
  let z : ParabolicPoint := (q.1, 1 / 2 + q.2)
  have hpre : (buGaussianTimeShiftPoint (1 / 2 : ℝ)).symm z = q := by
    rw [buGaussian_timeShift_point_symm_apply]
    apply Prod.ext
    · rfl
    · dsimp [z]
      ring
  calc
    _ = buGaussianTimeShiftPoint (1 / 2 : ℝ)
        ((buGaussianTimeShiftPoint (1 / 2 : ℝ)).symm z) :=
          congrArg _ hpre.symm
    _ = z := (buGaussianTimeShiftPoint (1 / 2 : ℝ)).apply_symm_apply z

/-- A dyadic cell translated forward by one half in time. -/
@[expose] def buShortShiftedDyadicCell (k : ℤ) (m : Fin 3 → ℤ)
    (ell : Fin 2048) : Set ParabolicPoint :=
  buGaussianTimeShiftPoint (1 / 2 : ℝ) ''
    Foundation.buSmallTimeDyadicCell k m ell

/-- A shifted dyadic cell lies inside its local energy cylinder
(`lem:bu-small-time`). -/
theorem bu_short_shifted_dyadic_cell_inner
    (k : ℤ) (m : Fin 3 → ℤ) (ell : Fin 2048) :
    let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
    let δ := (Foundation.buSmallTimeDyadicCellCenter k m ell).2
    let r := Real.sqrt δ / 8
    buShortShiftedDyadicCell k m ell ⊆
      spaceTimeSet (vec3Ball Y r)
        (Ioo (1 / 2 + δ - r ^ 2 / 2)
          (1 / 2 + δ - r ^ 2 / 2 + r ^ 2)) := by
  dsimp [buShortShiftedDyadicCell]
  rintro z ⟨q, hq, rfl⟩
  have hinner := bu_short_dyadic_cell_normalized_inner k m ell q hq
  have heval := bu_short_time_shift_point_eval q
  rw [heval]
  exact ⟨hinner.1, hinner.2⟩

end ESS
