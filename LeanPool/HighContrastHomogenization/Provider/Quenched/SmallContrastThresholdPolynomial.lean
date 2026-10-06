/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdaptedTilt
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEstimates
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowScale
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42CanonicalMetric

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastThresholdPolynomial

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The thresholds are polynomial

The near-reference comparison confines the reference aspect ratio to two scale
thresholds; the binder's sanctioned `Π`-slot is
`3^{m_0} ≤ (2 + Π·K)^{C_delay}`, so what must be checked is that three raised to
each threshold is polynomial in the data.  Both are, and both by the same
elementary bound `3^{max 1 ⌈y⌉} ≤ 3·max 1 (3^y)`:

* `3^{euclideanEntryThreshold K cEnt sK} ≤ 3^{sK}·3·max 1 (M₂(K)/cEnt)` — linear
  in the second source moment, i.e. polynomial in `K̄_S`; this is's first
  input, which the rework was predicted to shrink, and it does;
* `3^{tiltGap Cd g cEnt nu G} ≤ 3·max 1 ((2·boundaryConst·3^{gG}/cEnt)^{1/(1-g)})`
  — and at the fusion's binding `nu = canonicalMetric 𝐄`,
  `G = canonicalGridEnlargement d Π`, the base is polynomial in `Π` by
  `witnessEccentricity_canonicalMetric_le_aspectRatio`, so the whole gap is.
  The exponent `1/(1-g)` is the printed `(1-γ)^{-1}`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The elementary ceiling bound -/

/-- `3^{max 0 y} = max 1 3^y`. -/
private theorem three_rpow_max_zero (y : ℝ) :
    (3 : ℝ) ^ (max 0 y) = max 1 ((3 : ℝ) ^ y) := by
  rcases le_total 0 y with hy | hy
  · rw [max_eq_right hy, max_eq_right (Real.one_le_rpow (by norm_num) hy)]
  · rw [max_eq_left hy, Real.rpow_zero]
    refine (max_eq_left ?_).symm
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hy

/-- **The ceiling bound.**  `3^{max 1 ⌈y⌉} ≤ 3·max 1 (3^y)`: the integer-ceiling
analogue of `three_pow_ceil_logb_le`, which the two thresholds share. -/
theorem three_zpow_max_one_intCeil_le (y : ℝ) :
    (3 : ℝ) ^ (max 1 ⌈y⌉) ≤ 3 * max 1 ((3 : ℝ) ^ y) := by
  have hceil : ((⌈y⌉ : ℤ) : ℝ) ≤ y + 1 := by
    have h := Int.ceil_lt_add_one y
    exact h.le
  have hmaxeq : max 1 (y + 1) = 1 + max 0 y := by
    rcases le_total 0 y with hy | hy
    · rw [max_eq_right (by linarith only [hy]), max_eq_right hy]
      ring
    · rw [max_eq_left (by linarith only [hy]), max_eq_left hy]
      ring
  have hcast : (((max 1 ⌈y⌉ : ℤ)) : ℝ) ≤ 1 + max 0 y := by
    rw [Int.cast_max]
    refine le_trans (max_le_max (le_refl ((1 : ℤ) : ℝ)) hceil) ?_
    rw [Int.cast_one, hmaxeq]
  calc
    (3 : ℝ) ^ (max 1 ⌈y⌉) = (3 : ℝ) ^ (((max 1 ⌈y⌉ : ℤ)) : ℝ) :=
      (Real.rpow_intCast (3 : ℝ) _).symm
    _ ≤ (3 : ℝ) ^ (1 + max 0 y) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hcast
    _ = 3 * (3 : ℝ) ^ (max 0 y) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one]
    _ = 3 * max 1 ((3 : ℝ) ^ y) := by rw [three_rpow_max_zero]

/-! ## The Euclidean entry threshold -/

/-- **'s first input, at the rework's threshold.**  Three raised to the
Euclidean entry threshold is linear in the second source moment. -/
theorem three_zpow_euclideanEntryThreshold_le {K cEnt : ℝ} (hcEnt : 0 < cEnt)
    (sK : ℤ) :
    (3 : ℝ) ^ (euclideanEntryThreshold K cEnt sK) ≤
      (3 : ℝ) ^ sK * (3 * max 1 (sourceMomentTwo K / cEnt)) := by
  have hM0 : (0 : ℝ) < sourceMomentTwo K :=
    lt_of_lt_of_le zero_lt_one (one_le_sourceMomentTwo K)
  have hratio : (0 : ℝ) < sourceMomentTwo K / cEnt := div_pos hM0 hcEnt
  have hsK0 : (0 : ℝ) < (3 : ℝ) ^ sK := zpow_pos (by norm_num) _
  rw [euclideanEntryThreshold, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  refine mul_le_mul_of_nonneg_left ?_ hsK0.le
  refine le_trans (three_zpow_max_one_intCeil_le _) (le_of_eq ?_)
  rw [Real.rpow_logb (by norm_num) (by norm_num) hratio]

/-! ## The tilt gap -/

/-- **Three raised to the tilt gap is polynomial in the boundary envelope**,
with the printed `(1-γ)^{-1}` as the exponent. -/
theorem three_zpow_tiltGap_le {Cd g cEnt : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hcEnt : 0 < cEnt) {nu : Mat d} (hbase : 0 < boundaryConst Cd g nu) (G : ℕ) :
    (3 : ℝ) ^ (tiltGap Cd g cEnt nu G) ≤
      3 * max 1
        ((2 * boundaryConst Cd g nu * (3 : ℝ) ^ (g * (G : ℝ)) / cEnt) ^ (1 - g)⁻¹) := by
  have hg1 : (0 : ℝ) < 1 - g := by linarith only [hg.2]
  have h3G : (0 : ℝ) < (3 : ℝ) ^ (g * (G : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hA0 : (0 : ℝ) < 2 * boundaryConst Cd g nu * (3 : ℝ) ^ (g * (G : ℝ)) := by
    positivity
  have hratio : (0 : ℝ) <
      2 * boundaryConst Cd g nu * (3 : ℝ) ^ (g * (G : ℝ)) / cEnt := div_pos hA0 hcEnt
  rw [tiltGap]
  refine le_trans (three_zpow_max_one_intCeil_le _) (le_of_eq ?_)
  congr 2
  rw [div_eq_inv_mul (Real.logb 3 _) (1 - g), mul_comm ((1 - g)⁻¹),
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_logb (by norm_num) (by norm_num) hratio]

/-! ## The tilt gap at the fusion's binding is polynomial in `Π` -/

/-- The reference aspect ratio is at least one at a coarse-ellipticity
reference. -/
theorem one_le_aspectRatio_of_coarseEllipticityDagger [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    1 ≤ aspectRatio E :=
  le_trans (Initialization.one_le_refContrast_of_coarseEllipticityDagger hdag)
    (Initialization.refContrast_le_aspectRatio_of_coarseEllipticityDagger hdag)

end

end HCPolySupport.HighContrast.Quenched
