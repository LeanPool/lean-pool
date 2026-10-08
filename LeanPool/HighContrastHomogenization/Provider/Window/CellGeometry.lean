/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.Successor

/-!
# High-contrast homogenization: Provider.Window.CellGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Standard cells inside growing centered windows

The scale and center conditions used by the bad-scale supremum follow directly
from containment of a standard cell in the bounded window.  These elementary
facts keep the stopped-scale argument independent of a coordinate choice.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Centered triadic cubes increase with their generation. -/
theorem centeredCube_mono {m n : ℤ} (hmn : m ≤ n) :
    centeredCube d m ⊆ centeredCube d n := by
  intro x hx
  rw [Recurrence.mem_centeredCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num) hmn
  constructor <;> linarith only [(hx i).1, (hx i).2, hpow]

/-- A standard cell contained in a centered window cannot have larger scale
than the window. -/
theorem scale_le_of_standardCell_subset_centeredCube (hd : 0 < d) {k m : ℤ}
    {w : Fin d → ℤ} (hsub : standardCell d k w ⊆ centeredCube d m) : k ≤ m := by
  have hmeasure : volume (standardCell d k w) ≤ volume (centeredCube d m) :=
    measure_mono hsub
  have hfinite : volume (centeredCube d m) ≠ ⊤ := by
    exact (volume_openCubeSet_lt_top (originCube d m)).ne
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  simp only [standardCell, centeredCube, volume_openCubeSet_eq_volume_cubeSet,
    volume_cubeSet_toReal] at hreal
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale] at hreal
  change ((3 : ℝ) ^ k) ^ d ≤ ((3 : ℝ) ^ m) ^ d at hreal
  have hbase : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (Nat.ne_of_gt hd)).mp hreal
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hbase

/-- A cell in the original window meets the center and scale conditions of
every nonnegative enlargement. -/
theorem standardCell_data_in_enlargedWindow (hd : 0 < d) {k M : ℤ}
    {w : Fin d → ℤ} (hsub : standardCell d k w ⊆ centeredCube d M) (ℓ : ℕ) :
    k ≤ M + (ℓ : ℤ) ∧ standardCellCenter k w ∈ centeredCube d (M + (ℓ : ℤ)) := by
  have hkM : k ≤ M := scale_le_of_standardCell_subset_centeredCube hd hsub
  have hM : M ≤ M + (ℓ : ℤ) := by omega
  refine ⟨hkM.trans hM, centeredCube_mono hM (hsub ?_)⟩
  exact Recurrence.standardCellCenter_mem_standardCell k w

end

end Window
end HighContrast
end HCPolySupport
