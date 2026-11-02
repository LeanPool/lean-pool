/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseEps
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseWeights
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourSeminormComparisons

/-!
# StepFourCollapseInterface

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 4: the collapse of the excess-decay one-step into `hstep4`

## What this module is

`StepFiveIterationResult.iterationDecay_of_stepFourDecay` takes ONE
mathematical input, `hstep4`:

```lean
   ∀ j, n + k ≤ j → j ≤ m - 1 → j ∉ 𝓑_z →
     E(u, U_{j-k}) ≤ θ^k E(u, U_j) + ε_j |∇ℓ_j| + δ_j .
```

The excess-decay lane's anchored interior one-step delivers, at each scale `n`,
a display of the shape

```text
   E(u, U_{n-k}) ≤ C_con E(u, U_n)
       + C_rem · 3^{-n} · √((3²)^d) · ( T₁ + T₂ + T₃ + T₄ ) ,
   T₁ = C s^{-4} 𝓔_{n+1} ( ‖u-(u)‖_{L²(U_{n+1})} + s^{-3/2} 3^{n-2} |(∇h)_{U_n}| ) ,
   T₂ = C s^{-7} σ_{n-2}^{-1} 3^{(1+s)(n-2)} [g]_{H^s(U_{n+1})} ,
   T₃ = C s^{-6} 3^{(1+s)(n-2)} [∇h]_{H^s(U_{n+1})} ,
   T₄ = C s^{-6} 3^{n-2} ‖∇h‖_{L²(U_{n+1})} .
```

Every conversion is named and separately proved:

* `edLeg_one_le` — the `𝓔`-leg fold.  Its oscillation half is absorbed into the
  contraction (this is the term prices; see `StepFourCollapseWeights`), its
  slope half IS the `ε_j |∇ℓ_j|` leg, and its datum half is
  `s^{-3/2}·(1/9)·‖∇h‖_∞` (weight `three_weight_flat`).
* `edLeg_three_le` — the `∇h` seminorm leg, same collapse, no `σ`.
* `edLeg_four_le` — the `L²`-datum leg, weight `1/9`.

## The three mismatches, carried rather than absorbed

1. **The `ε`-slot carries a coefficient.**  The produced `ε` is
   `stepFourEpsCoeff · ε_j` with `stepFourEpsCoeff = C_rem V_d C s^{-4} C_osc`,
   NOT the raw `ε_j` at which `StepFiveIterationResult`'s `e.sum.eps.j.bound`
   slot is pinned (constant `2`).
2. **The gate scale shifts by one** — see `StepFourCollapseEps`; the produced
   `ε` reads `ε_{j+1}`.
3. **`δ_n`'s `∇h` legs are ungated, and one of them does not decay.**  The Step-5
   family multiplies its `∇h` legs by `1_{z ∉ □_{m-1}}` and its
   seminorm legs are `[·]_{W^{1/2,∞}(□_m)}`, whereas the excess-decay display
   carries them at every `z` and produces them at the Hölder constants `K_h`,
   `K_{h,∞}` (which DOMINATE those seminorms);
   moreover `T₄` collapses to the flat `C s^{-6}·(1/9)·‖∇h‖_∞`, with no decay in
   `n`, so its window sum is `(m-n+1)`-linear rather than `2δ(m-n)`-linear.
   The produced `δ` here is therefore `stepFourDeltaOut`, which is larger than
   the Step-5 family; feeding the Step-5 concrete endpoint at its own pinned
   family is not available from this display.

## The abstract excess-decay leg interface

The display above enters here as the hypothesis `hed` of
`stepFourDecay_of_edOneStep`, with the four leg values abstract reals and the
scale weights, the `3^{-n}` normalizer and the nesting written exactly as the
excess-decay lane's anchored interior one-step writes them.  The final stitch
is therefore one application: instantiate

```text
  Exc j := affineExcess (truncatedWindow z m j) u ,  Slp j := slopeMagnitude (g j) ,
  Ccon  := taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
             * (3^{-k})^{1/2} ,
  Crem  := triangleRemainderConst d (schauderWindowConst d) k ,
  Vd    := √((3²)^d) ,   Efl := fluxCorrectedErrorRepresentative … ,
```

and the six leg values at the display's own terms.

## References

* ABK26, `t.regularity` Step 4; `l.excess.decay.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The four leg conversions -/

/-- **The `𝓔`-leg conversion.**  `T₁`'s oscillation half folds into `C_osc (E +
|∇ℓ|)` (the hypothesis `hOsc` residue (2)) and its datum half collapses at the
flat weight `3^{-n} 3^{n-2} = 1/9`. -/
theorem edLeg_one_le {n : ℤ} {Cst s Efl Osc Gav epsj Cosc Khinf E0 S0 : ℝ}
    (hcoef : 0 ≤ Cst * s ^ (-(4 : ℝ))) (hw : 0 ≤ s ^ (-(3 / 2 : ℝ)))
    (hEfl : Efl ≤ epsj) (heps0 : 0 ≤ epsj)
    (hOsc0 : 0 ≤ (3 : ℝ) ^ (-n) * Osc)
    (hOsc : (3 : ℝ) ^ (-n) * Osc ≤ Cosc * (E0 + S0))
    (hGav0 : 0 ≤ Gav) (hGav : Gav ≤ Khinf) :
    (3 : ℝ) ^ (-n) *
        (Cst * s ^ (-(4 : ℝ)) * Efl *
          (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav)) ≤
      Cst * s ^ (-(4 : ℝ)) * epsj *
        (Cosc * (E0 + S0) + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) := by
  have hexp : (3 : ℝ) ^ (-n) *
      (Cst * s ^ (-(4 : ℝ)) * Efl *
        (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav)) =
      Cst * s ^ (-(4 : ℝ)) * Efl *
        ((3 : ℝ) ^ (-n) * Osc +
          s ^ (-(3 / 2 : ℝ)) *
            ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ))) * Gav) := by
    ring
  rw [hexp, three_weight_flat n]
  have hw9 : (0 : ℝ) ≤ s ^ (-(3 / 2 : ℝ)) * (1 / 9) := by
    have := mul_nonneg hw (by norm_num : (0 : ℝ) ≤ 1 / 9)
    linarith only [this]
  have hgav := mul_le_mul_of_nonneg_left hGav hw9
  have hbr : (3 : ℝ) ^ (-n) * Osc + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Gav ≤
      Cosc * (E0 + S0) + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf := by
    linarith only [hOsc, hgav]
  have hbr0 : 0 ≤ (3 : ℝ) ^ (-n) * Osc + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Gav := by
    have := mul_nonneg hw9 hGav0
    linarith only [hOsc0, this]
  have hc : Cst * s ^ (-(4 : ℝ)) * Efl ≤ Cst * s ^ (-(4 : ℝ)) * epsj :=
    mul_le_mul_of_nonneg_left hEfl hcoef
  exact mul_le_mul hc hbr hbr0 (mul_nonneg hcoef heps0)

/-- **The `g`-leg conversion: the shom-weight conversion in place.**  The
excess-decay leg's `σ_{n-2}^{-1}` becomes the Step-5 slot's `σ_n^{-1}` at the
absolute constant `8`, and the three scale factors collapse to `3^{n/2}`. -/
theorem edLeg_two_le {n : ℤ} {Cst s SigInv SigInvN Gsem Kg : ℝ}
    (hcoef : 0 ≤ Cst * s ^ (-(7 : ℝ))) (hs : 0 ≤ s)
    (hSig : SigInv ≤ 8 * SigInvN) (hSigN0 : 0 ≤ SigInvN)
    (hGsem0 : 0 ≤ Gsem) (hKg0 : 0 ≤ Kg)
    (hGsem : Gsem ≤ Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s))) :
    (3 : ℝ) ^ (-n) *
        (Cst * s ^ (-(7 : ℝ)) * SigInv *
          (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) ≤
      8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) := by
  have hP0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-n) := (zpow_pos (by norm_num) (-n)).le
  have hW10 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep1 : (3 : ℝ) ^ (-n) *
      ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) ≤ Kg * (3 : ℝ) ^ ((n : ℝ) / 2) := by
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hGsem hW10) hP0
    have h2 : (3 : ℝ) ^ (-n) *
        ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))) =
        Kg * ((3 : ℝ) ^ (-n) *
          ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))) := by
      ring
    have h3 := mul_le_mul_of_nonneg_left (three_weight_collapse_le n hs) hKg0
    linarith only [h1, h2, h3]
  have hexp : (3 : ℝ) ^ (-n) *
      (Cst * s ^ (-(7 : ℝ)) * SigInv *
        (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) =
      Cst * s ^ (-(7 : ℝ)) * SigInv *
        ((3 : ℝ) ^ (-n) * ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem)) := by
    ring
  rw [hexp]
  have hc : Cst * s ^ (-(7 : ℝ)) * SigInv ≤ Cst * s ^ (-(7 : ℝ)) * (8 * SigInvN) :=
    mul_le_mul_of_nonneg_left hSig hcoef
  have hX0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-n) *
      ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) :=
    mul_nonneg hP0 (mul_nonneg hW10 hGsem0)
  have hc0 : (0 : ℝ) ≤ Cst * s ^ (-(7 : ℝ)) * (8 * SigInvN) :=
    mul_nonneg hcoef (by linarith only [hSigN0])
  have hmain := mul_le_mul hc hstep1 hX0 hc0
  have hRHS : Cst * s ^ (-(7 : ℝ)) * (8 * SigInvN) * (Kg * (3 : ℝ) ^ ((n : ℝ) / 2)) =
      8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) := by
    ring
  linarith only [hmain, hRHS]

/-- **The `∇h`-seminorm leg conversion**: the same scale collapse, with no `σ`. -/
theorem edLeg_three_le {n : ℤ} {Cst s Hsem Kh : ℝ}
    (hcoef : 0 ≤ Cst * s ^ (-(6 : ℝ))) (hs : 0 ≤ s) (hKh0 : 0 ≤ Kh)
    (hHsem : Hsem ≤ Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s))) :
    (3 : ℝ) ^ (-n) *
        (Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) ≤
      Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) := by
  have hP0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-n) := (zpow_pos (by norm_num) (-n)).le
  have hW10 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hstep1 : (3 : ℝ) ^ (-n) *
      ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) ≤ Kh * (3 : ℝ) ^ ((n : ℝ) / 2) := by
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hHsem hW10) hP0
    have h2 : (3 : ℝ) ^ (-n) *
        ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
          (Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))) =
        Kh * ((3 : ℝ) ^ (-n) *
          ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) *
            (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))) := by
      ring
    have h3 := mul_le_mul_of_nonneg_left (three_weight_collapse_le n hs) hKh0
    linarith only [h1, h2, h3]
  have hexp : (3 : ℝ) ^ (-n) *
      (Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) =
      Cst * s ^ (-(6 : ℝ)) *
        ((3 : ℝ) ^ (-n) * ((3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem)) := by
    ring
  rw [hexp]
  have hmain := mul_le_mul_of_nonneg_left hstep1 hcoef
  have hRHS : Cst * s ^ (-(6 : ℝ)) * (Kh * (3 : ℝ) ^ ((n : ℝ) / 2)) =
      Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) := by
    ring
  linarith only [hmain, hRHS]

/-- **The `L²`-datum leg conversion**: the flat weight `1/9`.  This leg carries NO
decay in `n` — measured mismatch (3) of the module docstring. -/
theorem edLeg_four_le {n : ℤ} {Cst s Hl2 Khinf : ℝ}
    (hcoef : 0 ≤ Cst * s ^ (-(6 : ℝ))) (hHl2 : Hl2 ≤ Khinf) :
    (3 : ℝ) ^ (-n) *
        (Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2) ≤
      Cst * s ^ (-(6 : ℝ)) * ((1 / 9) * Khinf) := by
  have hexp : (3 : ℝ) ^ (-n) *
      (Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2) =
      Cst * s ^ (-(6 : ℝ)) *
        (((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ))) * Hl2) := by
    ring
  rw [hexp, three_weight_flat n]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hHl2 (by norm_num : (0 : ℝ) ≤ 1 / 9)) hcoef

/-! ## 2. The produced `ε`-coefficient and `δ_n` -/

/-- **The coefficient the collapse puts on `ε_j`.**  Measured mismatch (1): the
Step-5 `ε`-slot is pinned at the `ε_j`, this is `C_rem V_d C s^{-4} C_osc`
times it. -/
def stepFourEpsCoeff (Crem Vd Cst s Cosc : ℝ) : ℝ :=
  Crem * Vd * (Cst * s ^ (-(4 : ℝ))) * Cosc

/-- **The `δ_n` the collapse produces**, in the Step-5 slot's own weights: the
`g`-leg at `3^{n/2} σ_n^{-1} K_g` (constant `8` from the shom-weight
conversion), the `∇h` seminorm leg at `3^{n/2} K_h`, and the two flat datum
legs.  Larger than the Step-5 family — measured mismatch (3). -/
def stepFourDeltaOut (Crem Vd Cst s epsj Khinf SigInvN Kg Kh : ℝ) (n : ℤ) : ℝ :=
  Crem * Vd *
    (Cst * s ^ (-(4 : ℝ)) * epsj * (s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) +
      (8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) +
        (Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
          Cst * s ^ (-(6 : ℝ)) * ((1 / 9) * Khinf))))

/-- **The bracket bound**: the whole excess-decay remainder, split into the
absorbable contraction `(C_ε ε_j) E`, the `ε_j |∇ℓ|` leg, and `δ_n`. -/
theorem edBracket_le {n : ℤ}
    {Crem Vd Cst s Efl Osc Gav Gsem Hsem Hl2 SigInv SigInvN : ℝ}
    {epsj Kg Kh Khinf Cosc E0 S0 : ℝ}
    (hCV : 0 ≤ Crem * Vd) (hs : 0 ≤ s)
    (hcoef4 : 0 ≤ Cst * s ^ (-(4 : ℝ))) (hcoef6 : 0 ≤ Cst * s ^ (-(6 : ℝ)))
    (hcoef7 : 0 ≤ Cst * s ^ (-(7 : ℝ))) (hw : 0 ≤ s ^ (-(3 / 2 : ℝ)))
    (hEfl : Efl ≤ epsj) (heps0 : 0 ≤ epsj)
    (hOsc0 : 0 ≤ (3 : ℝ) ^ (-n) * Osc)
    (hOsc : (3 : ℝ) ^ (-n) * Osc ≤ Cosc * (E0 + S0))
    (hGav0 : 0 ≤ Gav) (hGav : Gav ≤ Khinf)
    (hSig : SigInv ≤ 8 * SigInvN) (hSigN0 : 0 ≤ SigInvN)
    (hGsem0 : 0 ≤ Gsem) (hKg0 : 0 ≤ Kg)
    (hGsem : Gsem ≤ Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hKh0 : 0 ≤ Kh)
    (hHsem : Hsem ≤ Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hHl2 : Hl2 ≤ Khinf) :
    Crem * ((3 : ℝ) ^ (-n) * (Vd *
        (Cst * s ^ (-(4 : ℝ)) * Efl *
            (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav) +
          Cst * s ^ (-(7 : ℝ)) * SigInv *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem +
          Cst * s ^ (-(6 : ℝ)) *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem +
            Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2))) ≤
      stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * E0 +
        (stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * S0 +
          stepFourDeltaOut Crem Vd Cst s epsj Khinf SigInvN Kg Kh n) := by
  have h1 := edLeg_one_le (n := n) (Cst := Cst) (s := s) (Efl := Efl) (Osc := Osc)
    (Gav := Gav) (epsj := epsj) (Cosc := Cosc) (Khinf := Khinf) (E0 := E0) (S0 := S0)
    hcoef4 hw hEfl heps0 hOsc0 hOsc hGav0 hGav
  have h2 := edLeg_two_le (n := n) (Cst := Cst) (s := s) (SigInv := SigInv)
    (SigInvN := SigInvN) (Gsem := Gsem) (Kg := Kg) hcoef7 hs hSig hSigN0 hGsem0 hKg0
    hGsem
  have h3 := edLeg_three_le (n := n) (Cst := Cst) (s := s) (Hsem := Hsem) (Kh := Kh)
    hcoef6 hs hKh0 hHsem
  have h4 := edLeg_four_le (n := n) (Cst := Cst) (s := s) (Hl2 := Hl2) (Khinf := Khinf)
    hcoef6 hHl2
  have hsum :
      (3 : ℝ) ^ (-n) *
          (Cst * s ^ (-(4 : ℝ)) * Efl *
            (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav)) +
        ((3 : ℝ) ^ (-n) *
            (Cst * s ^ (-(7 : ℝ)) * SigInv *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) +
          ((3 : ℝ) ^ (-n) *
              (Cst * s ^ (-(6 : ℝ)) *
                (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) +
            (3 : ℝ) ^ (-n) *
              (Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2))) ≤
        Cst * s ^ (-(4 : ℝ)) * epsj *
            (Cosc * (E0 + S0) + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) +
          (8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) +
            (Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
              Cst * s ^ (-(6 : ℝ)) * ((1 / 9) * Khinf))) := by
    linarith only [h1, h2, h3, h4]
  have hmul := mul_le_mul_of_nonneg_left hsum hCV
  have hleft : Crem * ((3 : ℝ) ^ (-n) * (Vd *
      (Cst * s ^ (-(4 : ℝ)) * Efl *
          (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav) +
        Cst * s ^ (-(7 : ℝ)) * SigInv *
            (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem +
        Cst * s ^ (-(6 : ℝ)) *
            (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem +
          Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2)))
      = Crem * Vd *
        ((3 : ℝ) ^ (-n) *
            (Cst * s ^ (-(4 : ℝ)) * Efl *
              (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav)) +
          ((3 : ℝ) ^ (-n) *
              (Cst * s ^ (-(7 : ℝ)) * SigInv *
                (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) +
            ((3 : ℝ) ^ (-n) *
                (Cst * s ^ (-(6 : ℝ)) *
                  (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) +
              (3 : ℝ) ^ (-n) *
                (Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2)))) := by
    ring
  have hright : Crem * Vd *
      (Cst * s ^ (-(4 : ℝ)) * epsj *
          (Cosc * (E0 + S0) + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) +
        (8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) +
          (Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
            Cst * s ^ (-(6 : ℝ)) * ((1 / 9) * Khinf))))
      = stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * E0 +
        (stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * S0 +
          stepFourDeltaOut Crem Vd Cst s epsj Khinf SigInvN Kg Kh n) := by
    rw [stepFourEpsCoeff, stepFourDeltaOut]
    ring
  linarith only [hmul, hleft, hright]

/-! ## 3. The endpoint: `hstep4`'s body at one scale -/

/-- **The Step-4 collapse.**  The excess-decay lane's one-step display (`hed`,
written exactly as the lane's anchored interior one-step writes it, with the six
leg values abstract) becomes the body of
`StepFiveIterationResult.iterationDecay_of_stepFourDecay`'s `hstep4` at the
scale `n`:

```text
   E_{n-k} ≤ θ^k E_n + (C_ε ε_j) |∇ℓ_n| + δ_n .
``` -/
theorem stepFourDecay_of_edOneStep {Exc Slp : ℤ → ℝ} {n : ℤ} {k : ℕ}
    {Ccon Crem Vd Cst s Efl Osc Gav Gsem Hsem Hl2 SigInv SigInvN : ℝ}
    {epsj Kg Kh Khinf Cosc thetaK : ℝ}
    (hCV : 0 ≤ Crem * Vd) (hs : 0 ≤ s)
    (hcoef4 : 0 ≤ Cst * s ^ (-(4 : ℝ))) (hcoef6 : 0 ≤ Cst * s ^ (-(6 : ℝ)))
    (hcoef7 : 0 ≤ Cst * s ^ (-(7 : ℝ))) (hw : 0 ≤ s ^ (-(3 / 2 : ℝ)))
    (hExc0 : 0 ≤ Exc n)
    (hEfl : Efl ≤ epsj) (heps0 : 0 ≤ epsj)
    (hOsc0 : 0 ≤ (3 : ℝ) ^ (-n) * Osc)
    (hOsc : (3 : ℝ) ^ (-n) * Osc ≤ Cosc * (Exc n + Slp n))
    (hGav0 : 0 ≤ Gav) (hGav : Gav ≤ Khinf)
    (hSig : SigInv ≤ 8 * SigInvN) (hSigN0 : 0 ≤ SigInvN)
    (hGsem0 : 0 ≤ Gsem) (hKg0 : 0 ≤ Kg)
    (hGsem : Gsem ≤ Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hKh0 : 0 ≤ Kh)
    (hHsem : Hsem ≤ Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hHl2 : Hl2 ≤ Khinf)
    (hCcon : Ccon ≤ thetaK / 2)
    (hTC34B : stepFourEpsCoeff Crem Vd Cst s Cosc * epsj ≤ thetaK / 2)
    (hed : Exc (n - (k : ℤ)) ≤ Ccon * Exc n +
      Crem * ((3 : ℝ) ^ (-n) * (Vd *
        (Cst * s ^ (-(4 : ℝ)) * Efl *
            (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav) +
          Cst * s ^ (-(7 : ℝ)) * SigInv *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem +
          Cst * s ^ (-(6 : ℝ)) *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem +
            Cst * s ^ (-(6 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2)))) :
    Exc (n - (k : ℤ)) ≤ thetaK * Exc n +
      (stepFourEpsCoeff Crem Vd Cst s Cosc * epsj) * Slp n +
      stepFourDeltaOut Crem Vd Cst s epsj Khinf SigInvN Kg Kh n := by
  have hbr := edBracket_le (n := n) (Crem := Crem) (Vd := Vd) (Cst := Cst) (s := s)
    (Efl := Efl) (Osc := Osc) (Gav := Gav) (Gsem := Gsem) (Hsem := Hsem) (Hl2 := Hl2)
    (SigInv := SigInv) (SigInvN := SigInvN) (epsj := epsj) (Kg := Kg) (Kh := Kh)
    (Khinf := Khinf) (Cosc := Cosc) (E0 := Exc n) (S0 := Slp n)
    hCV hs hcoef4 hcoef6 hcoef7 hw hEfl heps0 hOsc0 hOsc hGav0 hGav hSig hSigN0
    hGsem0 hKg0 hGsem hKh0 hHsem hHl2
  have hcomb : Exc (n - (k : ℤ)) ≤ Ccon * Exc n +
      (stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * Exc n +
        ((stepFourEpsCoeff Crem Vd Cst s Cosc * epsj) * Slp n +
          stepFourDeltaOut Crem Vd Cst s epsj Khinf SigInvN Kg Kh n)) := by
    linarith only [hed, hbr]
  have hfin := excess_absorb_two_contractions hExc0 hCcon hTC34B hcomb
  linarith only [hfin]

/-- The Step-4 `g`-comparison in the `toReal` shape the leg conversions consume: on
the Step-3 window `U_j = (z+□_j) ∩ □_m`, at any index `0 < s < 1/2`,

```text
   [g]_{H^s(U_j)} ≤ ( K · C_{S4.4}(d,s) ) · 3^{j(1/2-s)} ,
```

`K` the `C^{0,1/2}(□_m)` bound of `g`.  Instantiated at the excess-decay leg's
own window index `j := n+1` this is exactly `edLeg_two_le`'s /
`edLeg_three_le`'s hypothesis `hGsem` / `hHsem`, at `K_g := K · C_{S4.4}(d,s)`. -/
theorem stepFourGsemLeg_le {z : Vec d} {m j : ℤ} {g : Vec d → E} {K s : ℝ}
    (hd : 1 ≤ d) (hz : z ∈ openCubeSet (originCube d m)) (hs0 : 0 < s)
    (hs : s < 1 / 2) (hK : 0 ≤ K)
    (hg : Support.HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) K g) :
    (Support.normalizedGagliardoESeminormOn (stepThreeWindow z m j) s g).toReal ≤
      (K * stepFourGagliardoConst d s) * (3 : ℝ) ^ ((j : ℝ) * (1 / 2 - s)) := by
  have hnn : (0 : ℝ) ≤ K * stepFourGagliardoConst d s * (3 : ℝ) ^ ((j : ℝ) * (1 / 2 - s)) :=
    mul_nonneg (mul_nonneg hK (stepFourGagliardoConst_nonneg d s))
      (Real.rpow_nonneg (by norm_num) _)
  exact ENNReal.toReal_le_of_le_ofReal hnn
    (normalizedGagliardoESeminormOn_stepThreeWindow_le hd hz hs0 hs hK hg)

end

end Algsuperdiff.Section4.Provider.Regularity
