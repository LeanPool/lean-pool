/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitSource
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowScale
public import LeanPool.HighContrastHomogenization.Provider.Window.CellGeometry

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The carriers of the burn split: depth, anchor, window

The burn-split envelope needs a depth `D` doing three things at once: absorbing
the boundary constant (HC (2.123)), covering the canonical grid
enlargement so the aligned-cell containment is inherited, and being the height
of a coupled window so the mesoscale envelope is available at depth `2D`.

All three are met by one choice, `D = canonicalGridEnlargement d (C_d Π ζ_g)`,
with the window anchored at the burn scale built the way
`coupledExecBurn` builds its own — the ceiling that makes the coupling
inequality true by construction.  The anchor is a function of
`(d, g, Π, K, C_d)` alone, so the window threshold that the source scale
inherits is a delay and not a generation.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The burn depth: the grid enlargement built from the boundary constant's
own aspect ratio. -/
@[expose]
def burnSplitDepth (d : ℕ) (Cd g Pi : ℝ) : ℕ :=
  canonicalGridEnlargement d (Cd * Pi * zetaG g)

/-- The burn anchor, built as `coupledExecBurn` builds its own: the ceiling
that makes the coupling inequality true at height `2D`. -/
@[expose]
def burnSplitAnchor (d : ℕ) (Q K : ℝ) (D : ℕ) : ℤ :=
  max (sourceBurn d Q K)
    ⌈((d : ℝ) * (2 * (D : ℝ)) +
        16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
      (4 * (d : ℝ) + 3)⌉

private theorem one_le_zetaG {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    1 ≤ zetaG g := by
  have hlt : (3 : ℝ) ^ (-(1 - g)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg.2])
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(1 - g)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [zetaG]
  rw [le_inv_comm₀ (by norm_num) (by linarith only [hlt, hpos])]
  linarith only [hpos]

private theorem one_le_sqrt_dim (hd : 2 ≤ d) : (1 : ℝ) ≤ Real.sqrt d := by
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt d := Real.sqrt_le_sqrt h1

/-- The defining property of the enlargement: it dominates its own argument. -/
private theorem le_three_pow_canonicalGridEnlargement (hd : 2 ≤ d) {X : ℝ}
    (hX : 1 ≤ X) :
    (100 / 99 : ℝ) * X * Real.sqrt d ≤
      (3 : ℝ) ^ canonicalGridEnlargement d X := by
  have hsd : (1 : ℝ) ≤ Real.sqrt d := one_le_sqrt_dim hd
  have hy1 : (1 : ℝ) ≤ (100 / 99 : ℝ) * X * Real.sqrt d := by
    nlinarith only [hX, hsd]
  have hy0 : (0 : ℝ) < (100 / 99 : ℝ) * X * Real.sqrt d := by
    linarith only [hy1]
  calc (100 / 99 : ℝ) * X * Real.sqrt d
      = (3 : ℝ) ^ Real.logb 3 ((100 / 99 : ℝ) * X * Real.sqrt d) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hy0).symm
    _ ≤ (3 : ℝ) ^ ((canonicalGridEnlargement d X : ℕ) : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [canonicalGridEnlargement]
        exact Nat.le_ceil _
    _ = (3 : ℝ) ^ canonicalGridEnlargement d X := by
        rw [Real.rpow_natCast]

/-- **The depth absorbs the boundary constant.**  The Lean form of
HC (2.123) at this choice of depth. -/
theorem boundaryConst_le_three_pow_burnSplitDepth (hd : 2 ≤ d) {Cd g : ℝ}
    (hCd : 1 ≤ Cd) (hg : g ∈ Set.Ico (0 : ℝ) 1) {mAl : Mat d} {Pi : ℝ}
    (hPi : 1 ≤ Pi) (hecc : witnessEccentricity mAl ≤ Pi) :
    boundaryConst Cd g mAl ≤ (3 : ℝ) ^ burnSplitDepth d Cd g Pi := by
  have hz : (1 : ℝ) ≤ zetaG g := one_le_zetaG hg
  have hsd : (1 : ℝ) ≤ Real.sqrt d := one_le_sqrt_dim hd
  have hCdPi : (1 : ℝ) ≤ Cd * Pi := by nlinarith only [hCd, hPi]
  have hX : (1 : ℝ) ≤ Cd * Pi * zetaG g := by nlinarith only [hCdPi, hz]
  refine le_trans ?_ (le_three_pow_canonicalGridEnlargement hd hX)
  rw [boundaryConst]
  have hecc0 : 0 ≤ witnessEccentricity mAl := Real.sqrt_nonneg _
  have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd]
  have hz0 : (0 : ℝ) ≤ zetaG g := by linarith only [hz]
  have hbc : Cd * witnessEccentricity mAl * zetaG g ≤ Cd * Pi * zetaG g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hecc hCd0) hz0
  have hfac : (1 : ℝ) ≤ (100 / 99 : ℝ) * Real.sqrt d := by
    nlinarith only [hsd]
  have hup : Cd * Pi * zetaG g ≤
      (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d := by
    nlinarith only [hX, hfac]
  linarith only [hbc, hup]

/-- **The depth covers the grid enlargement, with a generation to spare.**  So
an aligned-cell containment stated at `t + G + 1` is inherited at `t + D`. -/
theorem succ_canonicalGridEnlargement_le_burnSplitDepth (hd : 2 ≤ d)
    {Cd g : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {Pi : ℝ} (hPi : 1 ≤ Pi) :
    canonicalGridEnlargement d Pi + 1 ≤ burnSplitDepth d Cd g Pi := by
  have hz : (1 : ℝ) ≤ zetaG g := one_le_zetaG hg
  have hsd : (1 : ℝ) ≤ Real.sqrt d := one_le_sqrt_dim hd
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hCdbig : 12 * (d : ℝ) * Real.sqrt d ≤ Cd := (le_max_right _ _).trans hCd
  have hCd24 : (24 : ℝ) ≤ Cd := by nlinarith only [hCdbig, hd2, hsd]
  have hy0 : (0 : ℝ) < (100 / 99 : ℝ) * Pi * Real.sqrt d := by
    nlinarith only [hPi, hsd]
  have hstep : Real.logb 3 ((100 / 99 : ℝ) * Pi * Real.sqrt d) + 1 ≤
      Real.logb 3 ((100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d) := by
    have hCz : (3 : ℝ) ≤ Cd * zetaG g := by nlinarith only [hCd24, hz]
    have hbase : (0 : ℝ) ≤ (100 / 99 : ℝ) * Pi * Real.sqrt d := hy0.le
    have hmul : (3 : ℝ) * ((100 / 99 : ℝ) * Pi * Real.sqrt d) ≤
        (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d := by
      calc (3 : ℝ) * ((100 / 99 : ℝ) * Pi * Real.sqrt d) ≤
          (Cd * zetaG g) * ((100 / 99 : ℝ) * Pi * Real.sqrt d) :=
            mul_le_mul_of_nonneg_right hCz hbase
        _ = (100 / 99 : ℝ) * (Cd * Pi * zetaG g) * Real.sqrt d := by ring
    have hlog := Real.logb_le_logb_of_le (b := 3) (by norm_num)
      (by linarith only [hy0] :
        (0 : ℝ) < (3 : ℝ) * ((100 / 99 : ℝ) * Pi * Real.sqrt d)) hmul
    have hsplit : Real.logb 3 ((3 : ℝ) * ((100 / 99 : ℝ) * Pi * Real.sqrt d)) =
        1 + Real.logb 3 ((100 / 99 : ℝ) * Pi * Real.sqrt d) := by
      rw [Real.logb_mul (by norm_num) (ne_of_gt hy0)]
      congr 1
      simp
    rw [hsplit] at hlog
    linarith only [hlog]
  rw [burnSplitDepth, canonicalGridEnlargement, canonicalGridEnlargement]
  refine le_trans (Nat.ceil_add_one ?_).ge ?_
  · exact Real.logb_nonneg (by norm_num)
      (by nlinarith only [hPi, hsd] :
        (1 : ℝ) ≤ (100 / 99 : ℝ) * Pi * Real.sqrt d)
  · exact Nat.ceil_le_ceil hstep

/-- **The window at the burn depth is coupled.**  The anchor is built by the
same ceiling that `coupledExecBurn` uses, so the coupling inequality holds by
construction. -/
theorem isCoupledWindow_burnSplitAnchor (hd : 2 ≤ d) {Q K : ℝ} {D : ℕ}
    (hD : 1 ≤ D) :
    IsCoupledWindow d Q K (burnSplitAnchor d Q K D)
      (burnSplitAnchor d Q K D + ((2 * D : ℕ) : ℤ)) := by
  have hden : (0 : ℝ) < 4 * (d : ℝ) + 3 := by positivity
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · have : (1 : ℤ) ≤ ((2 * D : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * D)
    omega
  · have hceil : ((⌈((d : ℝ) * (2 * (D : ℝ)) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3)⌉ : ℤ) : ℝ) ≥
        ((d : ℝ) * (2 * (D : ℝ)) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
          (4 * (d : ℝ) + 3) := Int.le_ceil _
    have hmax : (⌈((d : ℝ) * (2 * (D : ℝ)) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3)⌉ : ℤ) ≤ burnSplitAnchor d Q K D :=
      le_max_right _ _
    have hmaxR : ((⌈((d : ℝ) * (2 * (D : ℝ)) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3)⌉ : ℤ) : ℝ) ≤
        ((burnSplitAnchor d Q K D : ℤ) : ℝ) := by exact_mod_cast hmax
    have hcast : ((burnSplitAnchor d Q K D + ((2 * D : ℕ) : ℤ) : ℤ) : ℝ) -
        ((burnSplitAnchor d Q K D : ℤ) : ℝ) = 2 * (D : ℝ) := by
      push_cast
      ring
    rw [hcast]
    rw [ge_iff_le, div_le_iff₀ hden] at hceil
    nlinarith only [hceil, hmaxR, hden]

end

end HCPolySupport.HighContrast.Quenched
