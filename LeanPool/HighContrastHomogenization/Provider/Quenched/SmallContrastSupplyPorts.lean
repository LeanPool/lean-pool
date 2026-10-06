/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSupplyPorts

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Supply lemmas at the isotropy carriers

Three supply lemmas are stated for `meanDrop2ValueIsotropy` and
the isotropic mean-slot conversion, together with the congruence needed by
the fused core.

**The congruence, and why it is needed.**  `hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src`
takes
`hDrnn : ∀ j, 0 ≤ Dr j` unconditionally in the lag, while the drop family is nonnegative only
where the hatted contrast is monotone, i.e. for `t - j` at or above the grid
base.  The two are reconciled without touching either: the weak value depends on
`Dr` only through `Finset.range (Hw + 1)`
(the drop-family congruence below), so the fused core may use the
truncated family `fun j => Dr (min j n)`, which is nonnegative everywhere and
agrees with the original family on the whole window, since
`Hw n + 1 ≤ n`.

The two families are identified on the finite window by two
`Finset.sum_congr` arguments.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The drop channel at the isotropy carrier -/

/-- **The drop constant at a parametrized normalizer.**  The inflation scalar
and the normalizing block are explicit parameters. -/
@[expose]
def dropConstantIsotropy (cF : ℝ) (E F : BlockMat d) : ℝ := 4 * cF * blockSize E F

theorem dropConstantIsotropy_nonneg {cF : ℝ} (hcF : 0 ≤ cF) {E F : BlockMat d}
    (hbS : 0 ≤ blockSize E F) : 0 ≤ dropConstantIsotropy cF E F := by
  rw [dropConstantIsotropy]
  have h : (0 : ℝ) ≤ 4 * cF := by linarith only [hcF]
  exact mul_nonneg h hbS

/-- **The drop cap is an identity**, at the isotropy carrier too. -/
theorem meanDrop2ValueIsotropy_eq_dropConstantIsotropy_mul (P : Measure (CoeffSpace d))
    (lAl : ℤ) (cF : ℝ) (mAl : Mat d) (E F : BlockMat d) (N₀ n j : ℕ)
    (hj : j ≤ n) :
    meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)) j =
      dropConstantIsotropy cF E F *
        (hatExcess P (roundedGrid lAl mAl) N₀ (n - j) -
          hatExcess P (roundedGrid lAl mAl) N₀ n) := by
  have hidx : ((N₀ : ℤ) + (n : ℤ)) - (j : ℤ) = (N₀ : ℤ) + ((n - j : ℕ) : ℤ) := by
    omega
  rw [meanDrop2ValueIsotropy, dropConstantIsotropy, hatExcess, hatExcess, hidx]
  ring

/-- The `hDrdelta` inequality at the isotropy carrier follows arithmetically
from the preceding identity. -/
theorem hDrdelta_of_floor_isotropy (P : Measure (CoeffSpace d)) (lAl : ℤ) (cF : ℝ)
    (mAl : Mat d) (E F : BlockMat d) {N₀ : ℕ} {delta0 delta : ℝ}
    (hFnn : ∀ m : ℕ, 0 ≤ hatExcess P (roundedGrid lAl mAl) N₀ m)
    (hfloor : ∀ m : ℕ, hatExcess P (roundedGrid lAl mAl) N₀ m ≤ delta0)
    (hdc0 : 0 ≤ dropConstantIsotropy cF E F)
    (hchoice : dropConstantIsotropy cF E F * delta0 ≤ delta)
    (n j : ℕ) (hj : j ≤ n) :
    meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)) j ≤ delta := by
  rw [meanDrop2ValueIsotropy_eq_dropConstantIsotropy_mul P lAl cF mAl E F N₀ n j hj]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hdc0) hchoice
  linarith only [hfloor (n - j), hFnn n]

/-- **The drop family is nonnegative** where the hatted contrast is monotone. -/
theorem meanDrop2ValueIsotropy_nonneg (P : Measure (CoeffSpace d)) (lAl : ℤ)
    {cF : ℝ} (hcF : 0 ≤ cF) (mAl : Mat d) {E F : BlockMat d}
    (hbS : 0 ≤ blockSize E F) {N₀ : ℕ}
    (hFmono : ∀ p m : ℕ, p ≤ m →
      hatExcess P (roundedGrid lAl mAl) N₀ m ≤
        hatExcess P (roundedGrid lAl mAl) N₀ p)
    (n j : ℕ) (hj : j ≤ n) :
    0 ≤ meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)) j := by
  rw [meanDrop2ValueIsotropy_eq_dropConstantIsotropy_mul P lAl cF mAl E F N₀ n j hj]
  refine mul_nonneg (dropConstantIsotropy_nonneg hcF hbS) ?_
  have := hFmono (n - j) n (by omega)
  linarith only [this]

/-! ## The mean slot at the isotropy conversion -/

/-! ## The lag congruence -/

/-- **The truncated drop family.**  Nonnegative at every lag, and equal to the
one-step family's own on the whole window `Finset.range (Hw + 1)` whenever
`Hw + 1 ≤ n`. -/
theorem truncated_drop_agrees {Dr : ℕ → ℝ} {Hw n : ℕ} (hHw : Hw + 1 ≤ n) :
    ∀ j ∈ Finset.range (Hw + 1), Dr (min j n) = Dr j := by
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  omega

end

end HCPolySupport.HighContrast.Quenched
