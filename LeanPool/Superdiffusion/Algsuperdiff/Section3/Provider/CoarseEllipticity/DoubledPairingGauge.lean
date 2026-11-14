/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.BlockBesovPositive

/-!
# DoubledPairingGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The gauge conjugation of the Step-2 duality pairing

Source displays in ABK26:

* `e.form.of.A.naught`, the scalar reference matrix `bfA_0 = diag(sigma_0,
  sigma_0^{-1})` with `kappa_0 = 0`;
* the first display of Step 2 of `l.approximate.recurrence.formula`,
  ```
  fint_{z+cu_n} bfF_z . bfA_m tilde S_z
    <= [ bfAhom^{1/2} bfF_z ]_{H^1(z+cu_n)}
       [ bfAhom^{-1/2} bfA_m tilde S_z ]_{H^{-1}(z+cu_n)} .
  ```

## What the module supplies

The manuscript passes silently from the *ungauged* pairing `bfF_z. bfA_m tilde
S_z` to the *gauged* one, in which the negative seminorm is taken of
`bfAhom^{-1/2} bfA_m tilde S_z` and the positive seminorm of `bfAhom^{1/2}
bfF_z`.  Because `bfAhom_{m-h}` is the **scalar** block matrix `diag(sigma_0,
sigma_0^{-1})` (`e.homs.defs`, and the two sentences), that passage is the
exact pointwise identity

```
( bfA_0^{-1/2} u ) . ( bfA_0^{1/2} F ) = u . F ,
```

proved here as `blockVecDot_blockGaugeDown_blockGaugeUp`: the two diagonal
factors `sigma_0^{\pm 1/2}` cancel leg by leg.  No inequality is spent.

Composing it with the doubled duality bound of `BlockBesovPositive.lean` gives
`abs_cubeAverage_blockVecDot_le_besovDualityConst`, which is with the
manuscript's generic `C` pinned to `besovDualityConst`, and with the doubled
seminorms rendered as component sums.

Mean-zeroness of `bfF_z` enters here, and only here: it is what makes the
positive-seminorm leg a genuine cube fluctuation, so that the upstream duality
theorem -- which pairs against `cubeFluctuationVec` -- applies to the pairing
as printed.

## Binders

`0 < s` is the Besov exponent window; `0 < sig0` is the positivity of the
scalar `sigma_0` of `e.form.of.A.naught`; the four `L^2` memberships and the two
integrabilities are the hypotheses of the upstream componentwise duality
theorem; `hzero1`, `hzero2` are the mean-zeroness of the background of
`e.Fz.def` on its own cell.  `Bu` and `Bg` are caller-supplied seminorm
envelopes.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The scalar gauge `bfA_0^{\pm 1/2}` -/

/-- **`bfA_0^{1/2}` at the scalar `bfA_0 = diag(sigma_0, sigma_0^{-1})`.** -/
def blockGaugeUp (sig0 : ℝ) (X : BlockVec d) : BlockVec d :=
  (Real.sqrt sig0 • X.1, (Real.sqrt sig0)⁻¹ • X.2)

/-- **`bfA_0^{-1/2}` at the scalar `bfA_0 = diag(sigma_0, sigma_0^{-1})`.** -/
def blockGaugeDown (sig0 : ℝ) (X : BlockVec d) : BlockVec d :=
  ((Real.sqrt sig0)⁻¹ • X.1, Real.sqrt sig0 • X.2)

@[simp] theorem blockGaugeUp_fst (sig0 : ℝ) (X : BlockVec d) :
    (blockGaugeUp sig0 X).1 = Real.sqrt sig0 • X.1 := rfl

@[simp] theorem blockGaugeUp_snd (sig0 : ℝ) (X : BlockVec d) :
    (blockGaugeUp sig0 X).2 = (Real.sqrt sig0)⁻¹ • X.2 := rfl


/-- **The gauge conjugation identity.**  For a scalar `bfA_0`, conjugating the two
sides of a block pairing by `bfA_0^{\mp 1/2}` leaves the pairing unchanged.
This is the passage the manuscript performs between. -/
theorem blockVecDot_blockGaugeDown_blockGaugeUp {sig0 : ℝ} (hsig0 : 0 < sig0)
    (u F : BlockVec d) :
    blockVecDot (blockGaugeDown sig0 u) (blockGaugeUp sig0 F) = blockVecDot u F := by
  have hne : Real.sqrt sig0 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsig0)
  unfold blockGaugeDown blockGaugeUp blockVecDot
  rw [vecDot_smul_left, vecDot_smul_right, vecDot_smul_left, vecDot_smul_right]
  field_simp

/-- `blockVecDot` is symmetric. -/
theorem blockVecDot_comm (X Y : BlockVec d) : blockVecDot X Y = blockVecDot Y X := by
  unfold blockVecDot vecDot
  refine congrArg₂ (· + ·) ?_ ?_ <;>
    · refine Finset.sum_congr rfl ?_
      intro i _
      exact mul_comm _ _

/-! ## Fluctuations with vanishing cube average -/

/-- The cube average of a cube fluctuation vanishes. -/
theorem cubeAverageVec_cubeFluctuationVec (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverageVec Q (cubeFluctuationVec Q u) = 0 := by
  have h := cubeAverageVec_sub_const Q u (cubeAverageVec Q u) hu
  simpa [cubeFluctuationVec, sub_self] using! h

/-- A field with vanishing cube average is its own fluctuation. -/
theorem cubeFluctuationVec_eq_self_of_cubeAverageVec_eq_zero (Q : TriadicCube d)
    (u : Vec d → Vec d) (hu : cubeAverageVec Q u = 0) : cubeFluctuationVec Q u = u := by
  funext x
  simp [cubeFluctuationVec, hu]

/-- The gauged field of a mean-zero block field is its own doubled fluctuation.
-/
theorem blockCubeFluctuation_blockGaugeUp_eq_self (Q : TriadicCube d) (sig0 : ℝ)
    (F : Vec d → BlockVec d)
    (hzero1 : cubeAverageVec Q (fun x => (F x).1) = 0)
    (hzero2 : cubeAverageVec Q (fun x => (F x).2) = 0) :
    blockCubeFluctuation Q (fun x => blockGaugeUp sig0 (F x)) =
      fun x => blockGaugeUp sig0 (F x) := by
  have h1 : cubeAverageVec Q (fun x => (blockGaugeUp sig0 (F x)).1) = 0 := by
    change cubeAverageVec Q (fun x => Real.sqrt sig0 • (F x).1) = 0
    rw [cubeAverageVec_const_smul, hzero1, smul_zero]
  have h2 : cubeAverageVec Q (fun x => (blockGaugeUp sig0 (F x)).2) = 0 := by
    change cubeAverageVec Q (fun x => (Real.sqrt sig0)⁻¹ • (F x).2) = 0
    rw [cubeAverageVec_const_smul, hzero2, smul_zero]
  funext x
  refine Prod.ext ?_ ?_
  · change cubeFluctuationVec Q (fun y => (blockGaugeUp sig0 (F y)).1) x = _
    rw [cubeFluctuationVec_eq_self_of_cubeAverageVec_eq_zero Q _ h1]
  · change cubeFluctuationVec Q (fun y => (blockGaugeUp sig0 (F y)).2) x = _
    rw [cubeFluctuationVec_eq_self_of_cubeAverageVec_eq_zero Q _ h2]

/-! ## The pinned duality constant and the gauged pairing bound -/

/-- **The duality constant**, `2 d 3^{d+s} w(-s) w(s)`: the manuscript's generic
`C`, made explicit. -/
def besovDualityConst (Q : TriadicCube d) (s : ℝ) : ℝ :=
  2 * (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) *
    (cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q)

/-- ** with the gauge conjugation performed and the constant pinned.**

```
| fint_Q bfF_z . bfA_m tilde S_z |
  <= besovDualityConst Q s * ( Bu * Bg )
```

with `Bu` any envelope of the finite-depth negative `q = 2` Besov seminorms of
`bfA_0^{-1/2} bfA_m tilde S_z` and `Bg` any envelope of the finite-depth
positive ones of `bfA_0^{1/2} bfF_z`.

: `hs`, `hsig0`, the four `L^2` memberships, the two integrabilities and the
four seminorm envelopes are caller obligations, discharged at the caller's
carrier; `hzero1`, `hzero2` are the cell mean-zeroness of `e.Fz.def`. -/
theorem abs_cubeAverage_blockVecDot_le_besovDualityConst (Q : TriadicCube d) (s sig0 : ℝ)
    (F Y : Vec d → BlockVec d) {Bu Bg : ℝ}
    (hs : 0 < s) (hsig0 : 0 < sig0)
    (hY1 : MemLp (fun x => (Y x).1) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hY2 : MemLp (fun x => (Y x).2) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF1 : MemLp (fun x => (F x).1) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hF2 : MemLp (fun x => (F x).2) (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hBg : 0 ≤ Bg)
    (hzero1 : cubeAverageVec Q (fun x => (F x).1) = 0)
    (hzero2 : cubeAverageVec Q (fun x => (F x).2) = 0)
    (hInt1 : IntegrableOn
      (fun x => vecDot ((blockGaugeDown sig0 (Y x)).1)
        (cubeFluctuationVec Q (fun y => (blockGaugeUp sig0 (F y)).1) x))
      (cubeSet Q) volume)
    (hInt2 : IntegrableOn
      (fun x => vecDot ((blockGaugeDown sig0 (Y x)).2)
        (cubeFluctuationVec Q (fun y => (blockGaugeUp sig0 (F y)).2) x))
      (cubeSet Q) volume)
    (hneg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N
      (fun x => (blockGaugeDown sig0 (Y x)).1) ≤ Bu)
    (hneg2 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N
      (fun x => (blockGaugeDown sig0 (Y x)).2) ≤ Bu)
    (hpos1 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (blockGaugeUp sig0 (F x)).1) ≤ Bg)
    (hpos2 : ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N
      (fun x => (blockGaugeUp sig0 (F x)).2) ≤ Bg) :
    |cubeAverage Q (fun x => blockVecDot (F x) (Y x))| ≤
      besovDualityConst Q s * (Bu * Bg) := by
  have hsq : Real.sqrt sig0 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsig0)
  have hgY1 : MemLp (fun x => (blockGaugeDown sig0 (Y x)).1) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa [blockGaugeDown] using! hY1.const_smul ((Real.sqrt sig0)⁻¹)
  have hgY2 : MemLp (fun x => (blockGaugeDown sig0 (Y x)).2) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa [blockGaugeDown] using! hY2.const_smul (Real.sqrt sig0)
  have hgF1 : MemLp (fun x => (blockGaugeUp sig0 (F x)).1) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa [blockGaugeUp] using! hF1.const_smul (Real.sqrt sig0)
  have hgF2 : MemLp (fun x => (blockGaugeUp sig0 (F x)).2) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa [blockGaugeUp] using! hF2.const_smul ((Real.sqrt sig0)⁻¹)
  have hdual := abs_cubeAverage_blockVecDot_blockCubeFluctuation_le Q s
    (fun x => blockGaugeDown sig0 (Y x)) (fun x => blockGaugeUp sig0 (F x))
    hs hgY1 hgY2 hgF1 hgF2 hBg hInt1 hInt2 hneg1 hneg2 hpos1 hpos2
  rw [blockCubeFluctuation_blockGaugeUp_eq_self Q sig0 F hzero1 hzero2] at hdual
  have hpt : (fun x => blockVecDot (blockGaugeDown sig0 (Y x)) (blockGaugeUp sig0 (F x))) =
      fun x => blockVecDot (F x) (Y x) := by
    funext x
    rw [blockVecDot_blockGaugeDown_blockGaugeUp hsig0, blockVecDot_comm]
  rw [hpt] at hdual
  refine hdual.trans (le_of_eq ?_)
  unfold besovDualityConst
  ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
