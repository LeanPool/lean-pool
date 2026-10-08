/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCellRenormalization
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedFamily

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeRenormalizedWitness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The coupled mixing-scale witness from the frozen carriers

The renormalization of ellipticity feeds the bad-tail engine with a
generation-indexed family of minimal scales whose shifted tail is the engine's
`hRtail` at the dimensional constant `c_fr(d)`.  Its only analytic input is the
single-cell estimate `HasCellRenormalization`, and that estimate is now a
theorem of the frozen carriers.

This file performs the substitution: the reference family is the annealed block
at the inner generation `n - l₀`, the exponents are `γ = g` and `ν = d/2`, and
the gain is the dimensional constant `renormGain`.  What is left of the
hypothesis list is the engine's own bookkeeping — the parameters of the window,
the buffer, the block decay and the normalizer — together with three arithmetic
side conditions on the window: the inner generation lies below the base
generation, the window is no higher than `l₀ + 1`, and the source tail at the
lowest inner generation is at most one half.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open Book.Ch05.Section57

noncomputable section

variable {d : ℕ}

/-- The gain of the single-cell renormalization estimate on the frozen carriers:
a constant of the dimension, of the ellipticity exponent and of the reference
block alone. -/
@[expose]
def renormGain (d : ℕ) (g : ℝ) (E : BlockMat d) : ℝ :=
  32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * (1 + renormShift d) * kappaRef E

theorem renormGain_pos [NeZero d] {g : ℝ} {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hsharp : BlockMatLoewnerLE (blockSharp E) E) :
    0 < renormGain d g E := by
  have hd : (0 : ℝ) < (d : ℝ) := by
    have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast hd0
  have h3g : (0 : ℝ) < (3 : ℝ) ^ g := Real.rpow_pos_of_pos (by norm_num) _
  have hCfr : (0 : ℝ) < frThreshold d := frThreshold_pos d
  have hs : (0 : ℝ) ≤ renormShift d := renormShift_nonneg d
  have hk : (1 : ℝ) ≤ kappaRef E := Initialization.one_le_kappaRef hE hEpd hsharp
  have p1 : (0 : ℝ) < 32 * (d : ℝ) ^ 2 := by nlinarith only [hd]
  have p2 : (0 : ℝ) < 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g := mul_pos p1 h3g
  have p3 : (0 : ℝ) < 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d := mul_pos p2 hCfr
  have p4 : (0 : ℝ) < 32 * (d : ℝ) ^ 2 * (3 : ℝ) ^ g * frThreshold d * (1 + renormShift d) :=
    mul_pos p3 (by linarith only [hs])
  rw [renormGain]
  exact mul_pos p4 (by linarith only [hk])

/-- The annealed block at an inner generation is positive definite, the
reference comparison putting the positive reference block below it. -/
theorem blockPosDef_annealedBlock_of_frozen [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {Kg : ℝ}
    {S : CoeffSpace d → ℝ} (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi Kg S)
    (l : ℤ) (hhalf : (Psi ((3 : ℝ) ^ l))⁻¹ ≤ 1 / 2) :
    Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d l)) := by
  have href := blockMatLoewnerLE_blockScale_annealedBlock_reference hdag l
    (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag l) hhalf
  have hk1 : (1 : ℝ) ≤ kappaRef E :=
    Initialization.one_le_kappaRef hdag.refBlock_isSymm hdag.refBlock_posDef
      (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  intro X hX
  have h1 := href X
  rw [blockVecDot_blockMatVecMul_blockScale] at h1
  have hE := hdag.refBlock_posDef X hX
  by_contra hcon
  push Not at hcon
  have hneg : 2 * kappaRef E *
      blockVecDot X (blockMatVecMul (annealedBlock P (centeredCube d l)) X) ≤ 0 := by
    nlinarith only [hk1, hcon]
  linarith only [h1, hE, hneg]

end

end Quenched
end HighContrast
end HCPolySupport
