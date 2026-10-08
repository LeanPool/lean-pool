/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastPerGenerationRec

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSlotFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The depth-indexed variance slot family

Step 4 of, first half: the family `V : ℕ → ℝ` that
`exists_account_one_step_entry_of_block_at_level` consumes at every depth `j ≤ H_w`, assembled
from the two regimes of-13.2, and its summed bound — the `hVsum`
hypothesis of `weakValueSharpMajorant_le_three_group_summed_at_level`.

At the depth split `J = t - j_b`:

* `j ≤ J` (shallow): the leg's scale `p = t - j` satisfies `p ≥ j_b`, so the
  lagged supply is read at the base `j_b`, giving
  `slotSourceValue d Csub Msc (J - j) + slotBaseCoefficient d · F(j_b)`;
* `j > J` (deep): the supply is read at the leg's own scale, giving the
  constant `slotSourceValue d Csub Msc 0 + slotBaseCoefficient d · δ`.

Summing against the weight `3^{-j/2}` through `slot_source_sum_split_sharp` gives

  `vsum = (H_w+1)·(c₁+c₂+c₃)·3^{-J/2} + halfGeom·v₀`,
  `cVsum = halfGeom·(slotBaseCoefficient d + c₀)`,

with `c₁ = √(2d)·18·Csub·Msc`, `c₂ = √(2d)·288` and `c₃` the deep constant.
The source part decays in the generation through `J = ⌈n/4⌉`, which is what's obstruction required
and's rate `α = (1-g)/8` absorbs.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The total linear weight is below the geometric constant. -/
theorem linWeight_sum_le (Hw : ℕ) :
    ∑ j ∈ Finset.range (Hw + 1), linWeight j ≤ halfGeom := by
  have hrw : ∀ j ∈ Finset.range (Hw + 1),
      linWeight j = ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ j := fun j _ =>
    rpow_weight_eq_pow (mu := (1 / 2 : ℝ)) j
  rw [Finset.sum_congr rfl hrw]
  exact geom_sum_le_inv_one_sub
    (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)) _

/-- The deep-leg constant of the slot family. -/
@[expose]
def deepSlotConstant (d : ℕ) (Csub Msc delta : ℝ) : ℝ :=
  slotSourceValue d Csub Msc 0 + slotBaseCoefficient d * delta

/-- The source part of the slot family at depth `j`, split at `J`. -/
@[expose]
def slotSourceSeq (d : ℕ) (Csub Msc delta : ℝ) (J j : ℕ) : ℝ :=
  if j ≤ J then slotSourceValue d Csub Msc (J - j)
  else deepSlotConstant d Csub Msc delta

theorem slotSourceSeq_nonneg (d : ℕ) {Csub Msc delta : ℝ} (hCsub : 0 ≤ Csub)
    (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta) (J j : ℕ) :
    0 ≤ slotSourceSeq d Csub Msc delta J j := by
  rw [slotSourceSeq]
  split
  · exact slotSourceValue_nonneg d hCsub hMsc _
  · rw [deepSlotConstant]
    exact add_nonneg (slotSourceValue_nonneg d hCsub hMsc 0)
      (mul_nonneg (slotBaseCoefficient_nonneg d) hdelta)

/-- **The `hVsum` hypothesis of the summed split.**  Every slot bounded by its
source part plus a common multiple of the base excess gives the summed bound
with the two explicit constants. -/
theorem slot_sum_with_base {Hw : ℕ} {V : ℕ → ℝ} {vs : ℕ → ℝ}
    {cV Fjb V0 v0src cv0 vsrcSum : ℝ}
    (hcV : 0 ≤ cV) (hFjb : 0 ≤ Fjb)
    (hVj : ∀ j ∈ Finset.range (Hw + 1), V j ≤ vs j + cV * Fjb)
    (hV0 : V0 ≤ v0src + cv0 * Fjb) (hv0 : 0 ≤ v0src) (hcv0 : 0 ≤ cv0)
    (hvsSum : ∑ j ∈ Finset.range (Hw + 1), linWeight j * vs j ≤ vsrcSum) :
    ∑ j ∈ Finset.range (Hw + 1), linWeight j * (V j + V0) ≤
      (vsrcSum + halfGeom * v0src) +
        (halfGeom * (cV + cv0)) * Fjb := by
  classical
  have hterm : ∀ j ∈ Finset.range (Hw + 1),
      linWeight j * (V j + V0) ≤
        linWeight j * vs j + linWeight j * ((cV + cv0) * Fjb + v0src) := by
    intro j hj
    have hb := hVj j hj
    have hle : V j + V0 ≤ vs j + ((cV + cv0) * Fjb + v0src) := by
      linarith only [hb, hV0]
    have := mul_le_mul_of_nonneg_left hle (linWeight_nonneg j)
    linarith only [this]
  have hsplit := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsplit
  have hgeo := linWeight_sum_le Hw
  have hconst0 : (0 : ℝ) ≤ (cV + cv0) * Fjb + v0src := by
    have h1 : (0 : ℝ) ≤ (cV + cv0) * Fjb :=
      mul_nonneg (by linarith only [hcV, hcv0]) hFjb
    linarith only [h1, hv0]
  have hgeomul : (∑ j ∈ Finset.range (Hw + 1), linWeight j) *
      ((cV + cv0) * Fjb + v0src) ≤ halfGeom * ((cV + cv0) * Fjb + v0src) :=
    mul_le_mul_of_nonneg_right hgeo hconst0
  have hdist : halfGeom * ((cV + cv0) * Fjb + v0src) =
      halfGeom * v0src + halfGeom * (cV + cv0) * Fjb := by ring
  linarith only [hsplit, hgeomul, hvsSum, hdist.le, hdist.ge]

end

end HCPolySupport.HighContrast.Quenched
