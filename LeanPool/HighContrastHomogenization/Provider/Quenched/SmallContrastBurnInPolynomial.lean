/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourcePolynomial
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastDelayExponentUniform

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnInPolynomial

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-in is polynomial in the telescope's base

The `hentry` clause of the isotropic-variance core body reads

```
(3 : ℝ) ^ (2 * N₀) ≤ base ^ Centry
```

with `base = 2 + aspectRatio Ebase * Kbase` and `Centry` chosen **before** the
law.'s `entry_exponent_of_burnIn` reduces it to a law-free exponent for
`3 ^ N₀` itself, and the burn-in `N₀` the endpoint uses is the bootstrap's
`N1 = sK + 1 + gap` (`HCPoly.Provider.Quenched.SmallContrastBurnInUniform`).

This file closes's table.  Its two one-line entries are

* `witnessEccentricity_one` — the identity witness has eccentricity one, so
  `boundaryConst Cd g 1` is `(d, g)`-only and `bootstrapAdapterFactor Cd g K E 1`
  loses its grid factor entirely;
* `rpow_le_self_of_one_le` — `(1 + K ^ 2) ^ g ≤ 1 + K ^ 2` for `g ≤ 1`, which is
  what removes the source gauge's fractional power.

With them, every factor of `3 ^ N1 = 3 ^ sK * 3 * 3 ^ gap` is under a power of
the base: `3 ^ sK` by `exists_source_scale_minimal` and
`growthBar_le_base`, `3 ^ gap` by `exists_gap_three_pow_le_minimal` and the polynomial bound on
`bootstrapAdapterFactor` assembled here.
The law-free constants that remain — `CB`, `Cd`, `zetaG g`, `1 + 6 * sigma`,
`sigma⁻¹`, `3 ^ kZero d` — ride into the exponent through
`exists_rpow_ge_uniform`, which is admissible precisely because they are
fixed before `Ebase` and `Kbase`.

`sigma` is the endpoint's `cSc` step 6) and `CB`, `Cd` depend on `d` and
`g` alone, so `cburn` — and therefore `Cdelay` — is chosen at the binder's own
quantifier order.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## 1. The two one-line entries of -/

/-- **The identity witness has eccentricity one.**  `witnessEccentricity` is the
square root of `|m| |m⁻¹|`, and both factors are one at the identity. -/
theorem witnessEccentricity_one [Nonempty (Fin d)] :
    witnessEccentricity (1 : Mat d) = 1 := by
  have hspecinv : specBound ((1 : Mat d)⁻¹) = 1 := by
    rw [inv_one, specBound_eq_norm Matrix.PosSemidef.one, norm_one]
  have hspec : specBound (1 : Mat d) = 1 := by
    rw [specBound_eq_norm Matrix.PosSemidef.one, norm_one]
  rw [witnessEccentricity, hspec, hspecinv, mul_one, Real.sqrt_one]

/-- **A subunit power of a quantity at least one is below the quantity.**  At
`y := 1 + K ^ 2` and `c := g` this is `(1 + K ^ 2) ^ g ≤ 1 + K ^ 2`. -/
theorem rpow_le_self_of_one_le {y c : ℝ} (hy : 1 ≤ y) (hc : c ≤ 1) :
    y ^ c ≤ y := by
  have h := Real.rpow_le_rpow_of_exponent_le hy hc
  rwa [Real.rpow_one] at h

/-! ## 2. The bootstrap adapter factor at the identity witness -/

/-- The boundary constant at the identity witness is `(d, g)`-only. -/
theorem boundaryConst_one [Nonempty (Fin d)] (Cd g : ℝ) :
    boundaryConst Cd g (1 : Mat d) = Cd * zetaG g := by
  rw [boundaryConst, witnessEccentricity_one, mul_one]

/-- **The bootstrap adapter factor, polynomial in the growth bar.**  At the
identity witness the grid eccentricity is one, the source gauge's fractional
power collapses, and what remains is the reference ratio times the first source
moment times the `(d, g)`-only boundary constant. -/
theorem bootstrapAdapterFactor_one_le [Nonempty (Fin d)] {Cd g K sigma : ℝ}
    {E : BlockMat d} (hg1 : g ≤ 1) (hCd : 0 ≤ Cd)
    (hzeta : 0 ≤ zetaG g) (hsigma : 0 ≤ sigma)
    (hkap0 : 0 ≤ kappaRef E) (hkap : kappaRef E ≤ 1 + 6 * sigma) :
    bootstrapAdapterFactor Cd g K E (1 : Mat d) ≤
      (1 + K ^ 2) * ((1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g))) := by
  have hK1 : (1 : ℝ) ≤ 1 + K ^ 2 := by nlinarith only [sq_nonneg K]
  have hK0 : (0 : ℝ) ≤ 1 + K ^ 2 := by linarith only [hK1]
  have hgauge : (1 + K ^ 2) ^ g ≤ 1 + K ^ 2 := rpow_le_self_of_one_le hK1 hg1
  have hgauge0 : (0 : ℝ) ≤ (1 + K ^ 2) ^ g :=
    Real.rpow_nonneg hK0 g
  have hmom : sourceMomentOne K ≤ 3 * growthBar K ^ (1 : ℕ) := by
    have h := sourceMomentOne_le K
    have hT : IndependentSums.natTriangular 1 + 1 = 1 := by decide
    rwa [hT] at h
  have hmom' : sourceMomentOne K ≤ 3 * growthBar K := by
    rwa [pow_one] at hmom
  have hmom0 : (0 : ℝ) ≤ sourceMomentOne K := by
    have := one_le_sourceMomentOne (K := K)
    linarith only [this]
  have hbc0 : (0 : ℝ) ≤ Cd * zetaG g := mul_nonneg hCd hzeta
  have hkapb : (0 : ℝ) ≤ 1 + 6 * sigma := by linarith only [hsigma]
  have hstep1 : sourceMomentOne K * boundaryConst Cd g (1 : Mat d) ≤
      3 * growthBar K * (Cd * zetaG g) := by
    rw [boundaryConst_one]
    exact mul_le_mul_of_nonneg_right hmom' hbc0
  have hprod0 : (0 : ℝ) ≤ 3 * growthBar K * (Cd * zetaG g) := by
    have hG : (2 : ℝ) ≤ growthBar K := le_max_left 2 K
    have : (0 : ℝ) ≤ 3 * growthBar K := by linarith only [hG]
    exact mul_nonneg this hbc0
  have hmombc0 : (0 : ℝ) ≤ sourceMomentOne K * boundaryConst Cd g (1 : Mat d) := by
    rw [boundaryConst_one]
    exact mul_nonneg hmom0 hbc0
  have hratio : euclideanReferenceRatio Cd g K E ≤
      (1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g)) := by
    rw [euclideanReferenceRatio]
    calc kappaRef E * (sourceMomentOne K * boundaryConst Cd g (1 : Mat d))
        ≤ (1 + 6 * sigma) *
            (sourceMomentOne K * boundaryConst Cd g (1 : Mat d)) :=
          mul_le_mul_of_nonneg_right hkap hmombc0
      _ ≤ (1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g)) :=
          mul_le_mul_of_nonneg_left hstep1 hkapb
  have hratio0 : (0 : ℝ) ≤ euclideanReferenceRatio Cd g K E := by
    rw [euclideanReferenceRatio]
    exact mul_nonneg hkap0 hmombc0
  rw [bootstrapAdapterFactor, witnessEccentricity_one, one_mul]
  have hR0 : (0 : ℝ) ≤ (1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g)) :=
    mul_nonneg hkapb hprod0
  calc (1 + K ^ 2) ^ g * euclideanReferenceRatio Cd g K E
      ≤ (1 + K ^ 2) * euclideanReferenceRatio Cd g K E :=
        mul_le_mul_of_nonneg_right hgauge hratio0
    _ ≤ (1 + K ^ 2) * ((1 + 6 * sigma) * (3 * growthBar K * (Cd * zetaG g))) :=
        mul_le_mul_of_nonneg_left hratio hK0

/-! ## 3. The three factors combine -/

/-- **`3 ^ (sK + 1 + gap)` from its two factors.**  The `+ 1` of the burn-in
costs one power of the base, because the base is at least three. -/
theorem three_zpow_burnIn_le_rpow {base c1 c2 : ℝ} {sK gap : ℤ}
    (hbase : (3 : ℝ) ≤ base)
    (hsK : (3 : ℝ) ^ sK ≤ Real.rpow base c1)
    (hgap : (3 : ℝ) ^ gap ≤ Real.rpow base c2) :
    (3 : ℝ) ^ (sK + 1 + gap) ≤ Real.rpow base (c1 + c2 + 1) := by
  have hbase0 : (0 : ℝ) < base := by linarith only [hbase]
  have hsK0 : (0 : ℝ) < (3 : ℝ) ^ sK := by positivity
  have hgap0 : (0 : ℝ) < (3 : ℝ) ^ gap := by positivity
  have hsplit : (3 : ℝ) ^ (sK + 1 + gap) =
      (3 : ℝ) ^ sK * 3 * (3 : ℝ) ^ gap := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_one]
  have hrsplit : Real.rpow base (c1 + c2 + 1) =
      Real.rpow base c1 * Real.rpow base c2 * base := by
    show base ^ (c1 + c2 + 1) = base ^ c1 * base ^ c2 * base
    rw [Real.rpow_add hbase0, Real.rpow_add hbase0, Real.rpow_one]
  have h1 : (0 : ℝ) ≤ Real.rpow base c1 := le_trans hsK0.le hsK
  have h2 : (0 : ℝ) ≤ Real.rpow base c2 := le_trans hgap0.le hgap
  rw [hsplit, hrsplit]
  have hstep1 : (3 : ℝ) ^ sK * 3 ≤ Real.rpow base c1 * base := by
    have ha : (3 : ℝ) ^ sK * 3 ≤ Real.rpow base c1 * 3 :=
      mul_le_mul_of_nonneg_right hsK (by norm_num)
    have hb : Real.rpow base c1 * 3 ≤ Real.rpow base c1 * base :=
      mul_le_mul_of_nonneg_left hbase h1
    linarith only [ha, hb]
  have hstep2 : (3 : ℝ) ^ sK * 3 * (3 : ℝ) ^ gap ≤
      Real.rpow base c1 * base * Real.rpow base c2 := by
    have ha : (3 : ℝ) ^ sK * 3 * (3 : ℝ) ^ gap ≤
        Real.rpow base c1 * base * (3 : ℝ) ^ gap :=
      mul_le_mul_of_nonneg_right hstep1 hgap0.le
    have hb : Real.rpow base c1 * base * (3 : ℝ) ^ gap ≤
        Real.rpow base c1 * base * Real.rpow base c2 :=
      mul_le_mul_of_nonneg_left hgap
        (mul_nonneg h1 hbase0.le)
    linarith only [ha, hb]
  have hcomm : Real.rpow base c1 * base * Real.rpow base c2 =
      Real.rpow base c1 * Real.rpow base c2 * base := by ring
  linarith only [hstep2, hcomm.le, hcomm.ge]

/-! ## 4. The law-free burn-in exponent -/

end

end HCPolySupport.HighContrast.Quenched
