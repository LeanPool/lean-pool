/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineInstallPins

/-!
# HomSpineResiduePairing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `EthmB(m)` pairing: the two printed summands, against the two level slots

## What this file supplies

`HomSpineInstallArith` reduced the §4.5 level arithmetic to three residues, of
which two — `hA`, `hB` together with the budget split `hsplit` — are the
manuscript's "comparing to the definition of `EthmB(m)`".  This
file performs that comparison at the two printed summands of `EthmB(m)`:

```text
  EthmB(m) = s^{-1} 3^{(1-α)X_m(α)} 𝓔_{s₁}(□_m,n) (1 + 𝓔_{1/4}(□_m))
               + C γ⁵ (1 + 𝓔²_{s₁/2}(□_m,n)).
```

* `ofReal_firstLeg_le` pairs the FIRST level slot `C_cg σ⁻¹ 𝓔₁ C_en` against the
  first summand.  The Step-2 constant `C_en` is taken at the shape the printed
  energy-density bound gives it — `C_en = C · (3^{(1-α)X_m}
  (1 + 𝓔_{1/4}))` — which is what makes the pairing an inequality between the
  SAME two random factors.
* the gap leg pairs the SECOND level slot against the `γ⁵` summand,
  through `HomSpineInstallData.homGapAbsorbAt` at any `s₂`
  admitting the absorption, in particular the corrected pin `s₂ = 49/100`.
* `ofReal_add_le_ethmB` adds the two, and `le_toReal_of_ofReal_le` converts the
  `[0,∞]` domination into the REAL budget inequality `A + B ≤ C_w · E_B` that
  the bundle's `hsplit` conjunct is, at `E_B:= (EthmB(m))(ω).toReal`.

The two `𝓔`-dominations are the file's inputs, stated at the own
carriers; see the disclosure below.

## Scope

The two hypotheses `hdom1`, `hdom2` compare the coarse-graining bundle's error
slots with `EthmB(m)`'s own factors.  At the CURRENT pins these two
are NOT the same object, in three independent respects, and no bridge between
them exists in the tree:

1. **the coefficient** — the bundle's slots dominate
   `parentTruncatedHomogenizationErrorInfinity{One,Two}Scalar` at the CUTOFF
   field `a_L` (`Cutoff.coefficientCutoffCoeffOn`), while `EthmB(m)` and BOTH printed
   displays carry the FLUX-CORRECTED field
   `ã_{L,m}`;
2. **the order** — the bundle pins the dual low order at `s₁′ = s/8` (and its
   half `s/16`), while `EthmB(m)` carries `s₁ = s/2` (and `s₁/2 = s/4`), the
   print's own choice the §4.5 parameter choices.  `𝓔` is a weighted average
   with normalized weights and is NOT monotone in the order, so neither
   direction is free;
3. **the `q` index** — the first slot's carrier is the `q = 1` functional,
   `EthmB(m)`'s first factor the `q = 2` one (the print has the same asymmetry
   between the two printed displays, where it is a Jensen step).

Nothing in this file asserts those inputs; they are named, and the arithmetic
above them is proved outright.
-/

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The two summands of `EthmB(m)`, named -/

/-- The FIRST summand of `EthmB(m)`: the minimal-scale factor
times the two printed `𝓔` factors, weighted by `s^{-1}`. -/
def ethmBFirst (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ENNReal.ofReal ((s : ℝ)⁻¹) *
    (Y omega *
      (fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega *
        (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)))

/-- The SECOND summand of `EthmB(m)`: the `γ⁵` gap term. -/
def ethmBGap (M : ABKModel d) (Cgap : ℝ) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ENNReal.ofReal (Cgap * M.gamma ^ (5 : ℕ)) *
    (1 +
      fluxCorrectedTwoScaleErrorObservableSup M m n (homQuarterOf s) omega ^ (2 : ℝ))

/-- `EthmB(m)` IS the sum of its two named summands. -/
theorem ethmB_eq_first_add_gap (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) :
    ethmB M Cgap Y m n s omega =
      ethmBFirst M Y m n s omega + ethmBGap M Cgap m n s omega :=
  rfl

/-! ## 2. The first leg: the level's first slot against the first summand -/

/-- The abstract shape of the first pairing: a real product with one `toReal`
factor, against the `[0,∞]` product it is a `toReal` of. -/
private theorem ofReal_firstLeg_core {c Cen0 E1 sr : ℝ} (Ycar Qcar Rcar : ℝ≥0∞)
    (hc : 0 ≤ c) (hCen0 : 0 ≤ Cen0) (hE1 : 0 ≤ E1) (hsr : 0 < sr)
    (hdom : ENNReal.ofReal E1 ≤ Qcar) :
    ENNReal.ofReal (c * E1 * (Cen0 * (Ycar * Rcar).toReal)) ≤
      ENNReal.ofReal (c * Cen0 * sr) *
        (ENNReal.ofReal sr⁻¹ * (Ycar * (Qcar * Rcar))) := by
  have hcCen : (0 : ℝ) ≤ c * Cen0 := mul_nonneg hc hCen0
  have hlhs : ENNReal.ofReal (c * E1 * (Cen0 * (Ycar * Rcar).toReal)) =
      ENNReal.ofReal (c * Cen0) *
        (ENNReal.ofReal E1 * ENNReal.ofReal (Ycar * Rcar).toReal) := by
    rw [show c * E1 * (Cen0 * (Ycar * Rcar).toReal) =
        c * Cen0 * (E1 * (Ycar * Rcar).toReal) by ring,
      ENNReal.ofReal_mul hcCen, ENNReal.ofReal_mul hE1]
  have hconst : ENNReal.ofReal (c * Cen0 * sr) * ENNReal.ofReal sr⁻¹ =
      ENNReal.ofReal (c * Cen0) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hcCen hsr.le)]
    congr 1
    field_simp
  have hrhs : ENNReal.ofReal (c * Cen0 * sr) *
      (ENNReal.ofReal sr⁻¹ * (Ycar * (Qcar * Rcar))) =
      ENNReal.ofReal (c * Cen0) * (Qcar * (Ycar * Rcar)) := by
    rw [← mul_assoc, hconst]
    ring
  rw [hlhs, hrhs]
  exact mul_le_mul' le_rfl (mul_le_mul' hdom ENNReal.ofReal_toReal_le)

/-- **THE FIRST PAIRING**.

The level's first slot — the coarse-graining constant, the order weight, the
error slot and the Step-2 constant `C_en` at its printed shape
`C · (3^{(1-α)X_m}(1 + 𝓔_{1/4}))` — is below the first summand of `EthmB(m)`
times a constant that carries no randomness.

The single input is `hdom`: the error slot is dominated by `EthmB(m)`'s own
first `𝓔` factor.  See the module disclosure. -/
theorem ofReal_firstLeg_le (M : ABKModel d) (Y : Cutoff.CutoffSample d → ℝ≥0∞)
    (m n : ℤ) (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d)
    {c Cen0 E1 : ℝ} (hc : 0 ≤ c) (hCen0 : 0 ≤ Cen0) (hE1 : 0 ≤ E1)
    (hdom : ENNReal.ofReal E1 ≤
      fluxCorrectedTwoScaleErrorObservableSup M m n (homHalf s) omega) :
    ENNReal.ofReal
        (c * E1 *
          (Cen0 *
            (Y omega *
              (1 + fluxCorrectedTwoScaleErrorObservableSup M m m homQuarter omega)).toReal)) ≤
      ENNReal.ofReal (c * Cen0 * (s : ℝ)) * ethmBFirst M Y m n s omega :=
  ofReal_firstLeg_core _ _ _ hc hCen0 hE1 s.2 hdom

/-! ## 3. The second leg: the level's forcing slot against the `γ⁵` summand -/

/-- The gap-absorption constant is nonnegative exactly on the range where the
absorption holds. -/
theorem homGapConstAt_nonneg {s2 : ℝ} (hs2 : 5 < 10 * s2 * Real.log 3) :
    0 ≤ homGapConstAt s2 := by
  have hpos : (0 : ℝ) < 10 * s2 * Real.log 3 - 5 := by linarith only [hs2]
  rw [homGapConstAt]
  positivity

/-! ## 4. The two legs added: the budget inequality -/

/-- **THE `EthmB(m)` BUDGET, in `[0,∞]`.**  Both level slots together are below
`EthmB(m)` times the sum of the two pairing constants. -/
theorem ofReal_add_le_ethmB (M : ABKModel d) (Cgap : ℝ)
    (Y : Cutoff.CutoffSample d → ℝ≥0∞) (m n : ℤ) (s : {s : ℝ // 0 < s})
    (omega : Cutoff.CutoffSample d) {A B cA cB : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB)
    (hA : ENNReal.ofReal A ≤ ENNReal.ofReal cA * ethmBFirst M Y m n s omega)
    (hB : ENNReal.ofReal B ≤ ENNReal.ofReal cB * ethmBGap M Cgap m n s omega) :
    ENNReal.ofReal (A + B) ≤
      ENNReal.ofReal (cA + cB) * ethmB M Cgap Y m n s omega := by
  have hcA : ENNReal.ofReal cA ≤ ENNReal.ofReal (cA + cB) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hcB0])
  have hcB : ENNReal.ofReal cB ≤ ENNReal.ofReal (cA + cB) :=
    ENNReal.ofReal_le_ofReal (by linarith only [hcA0])
  calc ENNReal.ofReal (A + B)
      = ENNReal.ofReal A + ENNReal.ofReal B := ENNReal.ofReal_add hA0 hB0
    _ ≤ ENNReal.ofReal cA * ethmBFirst M Y m n s omega +
          ENNReal.ofReal cB * ethmBGap M Cgap m n s omega := add_le_add hA hB
    _ ≤ ENNReal.ofReal (cA + cB) * ethmBFirst M Y m n s omega +
          ENNReal.ofReal (cA + cB) * ethmBGap M Cgap m n s omega :=
        add_le_add (mul_le_mul' hcA le_rfl) (mul_le_mul' hcB le_rfl)
    _ = ENNReal.ofReal (cA + cB) *
          (ethmBFirst M Y m n s omega + ethmBGap M Cgap m n s omega) := by ring
    _ = ENNReal.ofReal (cA + cB) * ethmB M Cgap Y m n s omega := by
        rw [ethmB_eq_first_add_gap]

/-! ## 5. The real budget: the bundle's `hsplit`, at `E_B = (EthmB(m)).toReal` -/

/-- **THE REAL CUT.**  An `[0,∞]` domination by `C_w · EthmB(m)` becomes the
bundle's own real budget inequality at `E_B:= (EthmB(m))(ω).toReal`, on the
(a.e.) event where the carrier is finite. -/
theorem le_toReal_of_ofReal_le {X Cw : ℝ} {T : ℝ≥0∞} (hCw : 0 ≤ Cw)
    (hfin : T ≠ ⊤) (h : ENNReal.ofReal X ≤ ENNReal.ofReal Cw * T) :
    X ≤ Cw * T.toReal := by
  have hT : ENNReal.ofReal Cw * T = ENNReal.ofReal (Cw * T.toReal) := by
    rw [ENNReal.ofReal_mul hCw, ENNReal.ofReal_toReal hfin]
  rw [hT] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCw ENNReal.toReal_nonneg)).1 h

end

end Algsuperdiff.Section4.Provider.Homogenization
