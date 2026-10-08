/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.RoundedGrid
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.CheckpointMoment
public import LeanPool.HighContrastHomogenization.Setup.SpectralNorm
public import LeanPool.HighContrastHomogenization.Setup.SourceObjects

/-!
# High-contrast homogenization: Provider.Initialization.IdentityGrid

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The rounded identity grid

At the nonnegative alignment supplied by a coupled window, every diagonal
entry being rounded is the integer `3^j` and every off-diagonal entry is zero.
Rescaling therefore returns the identity exactly.
-/

namespace HCPolySupport
namespace HighContrast
namespace Initialization

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Centered triadic cubes are nested with their integer scale. -/
theorem centeredCube_subset_centeredCube {r M : ℤ} (hrM : r ≤ M) :
    centeredCube d r ⊆ centeredCube d M := by
  intro x hx
  rw [Recurrence.mem_centeredCube_iff] at hx ⊢
  have hpow : (3 : ℝ) ^ r ≤ (3 : ℝ) ^ M :=
    zpow_le_zpow_right₀ (by norm_num) hrM
  intro i
  constructor
  · linarith only [hpow, (hx i).1]
  · linarith only [hpow, (hx i).2]

/-- The adapted cell of the identity grid is the centered triadic cube. -/
theorem adaptedCell_one (r : ℤ) :
    adaptedCell (1 : Mat d) r = centeredCube d r := by
  rw [adaptedCell]
  have hone : matVecMul (1 : Mat d) = fun x => x := by
    funext x i
    change Matrix.mulVec (1 : Mat d) x i = x i
    rw [Matrix.one_mulVec]
  rw [hone, Set.image_id']

/-- The identity witness is fixed by rounding at the alignment of a coupled
window. -/
theorem roundedGrid_one {Q K : ℝ} {jStar M : ℤ}
    [Nonempty (Fin d)] (hw : IsCoupledWindow d Q K jStar M) :
    roundedGrid jStar (1 : Mat d) = (1 : Mat d) := by
  have hk : (kZero d : ℤ) ≤ jStar := by
    have hburn : (kZero d : ℤ) ≤ sourceBurn d Q K := by
      rw [sourceBurn]
      exact le_max_left _ _
    exact hburn.trans hw.1
  have hj0 : 0 ≤ jStar := (Int.natCast_nonneg _).trans hk
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
  have hspec : specBound ((1 : Mat d)⁻¹) = 1 := by
    rw [inv_one, specBound_eq_norm Matrix.PosSemidef.one, norm_one]
  ext i k
  rw [Recurrence.roundedGrid_apply, hspec, Real.sqrt_one, Recurrence.matSqrt_one]
  by_cases hik : i = k
  · subst k
    simp only [Matrix.one_apply_eq, mul_one, zpow_natCast]
    have hceil : ⌈(3 : ℝ) ^ n⌉ = (((3 ^ n : ℕ) : ℤ)) := by
      simpa only [Nat.cast_ofNat, Nat.cast_pow] using
        (Int.ceil_natCast (R := ℝ) (3 ^ n))
    rw [hceil, Int.cast_natCast, zpow_neg, zpow_natCast, Nat.cast_pow]
    exact inv_mul_cancel₀ (by positivity)
  · simp [hik, zpow_natCast]

/-- Every identity-grid scale in the window range is an admissible centered
index. -/
theorem identity_admissible_index {Q K : ℝ} {jStar M r : ℤ}
    [Nonempty (Fin d)] (hw : IsCoupledWindow d Q K jStar M)
    (hjr : jStar ≤ r) (hrM : r ≤ M) :
    IsAdmissibleIndex (roundedGrid jStar (1 : Mat d)) jStar M r 0 := by
  have hsub : centeredCube d r ⊆ centeredCube d M :=
    centeredCube_subset_centeredCube hrM
  rw [roundedGrid_one hw]
  refine ⟨hjr, ?_, ?_⟩
  · rw [PortableHistory.adaptedCellAt_zero, adaptedCell_one]
    exact hsub
  · rw [adaptedCell_one]
    exact hsub

end

end Initialization
end HighContrast
end HCPolySupport
