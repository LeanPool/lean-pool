/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixBoundaryIterationC1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBCloseChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBGateGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaChain

/-!
# RootClauseBGateBoundaryC1

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The outer collapse with the `H` leg kept -/

/-- **The clause-(B) bracket collapse on the boundary branch.**

`RootClauseBArith.rootClauseB_collapse` with `H ≠ 0`: the chain's data bracket
splits as `√σ_m^{-1}(W·G) + √σ_m(W·H)`, and the two dominations `W·G ≤
C_WG·L_g`, `W·H ≤ C_WH·L_h` carry it onto the printed three-leg bracket.

Pure arithmetic: every domination is a hypothesis, `Real.rpow` and `Real.sqrt`
are opaque throughout, and no estimate is derived. -/
theorem rootClauseB_collapse_boundary
    {E Kmain Kdata Ccol CdG CWG CWH CdM shomM gradLoc gradM dataG dataM
      W G H Lg Lh : ℝ}
    (hKmain : 0 ≤ Kmain) (hKdata : 0 ≤ Kdata) (hCcol : 0 ≤ Ccol)
    (hCWG : 0 ≤ CWG) (hCWH : 0 ≤ CWH) (hCdM : 0 ≤ CdM) (hE : 0 ≤ E)
    (hgradM : 0 ≤ gradM) (hLg : 0 ≤ Lg) (hLh : 0 ≤ Lh)
    (hWG0 : 0 ≤ W * G) (hWH0 : 0 ≤ W * H) (hdataM0 : 0 ≤ dataM)
    (hdataG : dataG ≤ CdG * Lg)
    (hWG : W * G ≤ CWG * Lg)
    (hWH : W * H ≤ CWH * Lh)
    (hdataM : dataM ≤ CdM * (Real.sqrt shomM⁻¹ * Lg))
    (h : gradLoc ≤
      Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
          (Ccol *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H)) + dataM)) :
    gradLoc ≤
      (Kmain * max 1 CdG + Kdata * (Ccol * CWG + Ccol * CWH + CdM)) *
        Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
  have hSI : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ := Real.sqrt_nonneg _
  have hS : (0 : ℝ) ≤ Real.sqrt shomM := Real.sqrt_nonneg _
  have hinv : (Real.sqrt shomM)⁻¹ = Real.sqrt shomM⁻¹ := (Real.sqrt_inv shomM).symm
  have hR : (0 : ℝ) ≤ Real.rpow (3 : ℝ) E := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hLegG : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ * Lg := mul_nonneg hSI hLg
  have hLegH : (0 : ℝ) ≤ Real.sqrt shomM * Lh := mul_nonneg hS hLh
  have hT : (0 : ℝ) ≤ gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh := by
    linarith only [hgradM, hLegG, hLegH]
  -- the bracket, split
  have hbr : W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * H) =
      Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H) := by
    rw [hinv]; ring
  rw [hbr] at h
  -- the two data legs against the printed bracket
  have hoscG : Real.sqrt shomM⁻¹ * (W * G) ≤
      CWG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep : Real.sqrt shomM⁻¹ * (W * G) ≤ Real.sqrt shomM⁻¹ * (CWG * Lg) :=
      mul_le_mul_of_nonneg_left hWG hSI
    have hid : Real.sqrt shomM⁻¹ * (CWG * Lg) = CWG * (Real.sqrt shomM⁻¹ * Lg) := by
      ring
    have hgrow : CWG * (Real.sqrt shomM⁻¹ * Lg) ≤
        CWG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM, hLegH]) hCWG
    linarith only [hstep, hid, hgrow]
  have hoscH : Real.sqrt shomM * (W * H) ≤
      CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep : Real.sqrt shomM * (W * H) ≤ Real.sqrt shomM * (CWH * Lh) :=
      mul_le_mul_of_nonneg_left hWH hS
    have hid : Real.sqrt shomM * (CWH * Lh) = CWH * (Real.sqrt shomM * Lh) := by ring
    have hgrow : CWH * (Real.sqrt shomM * Lh) ≤
        CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM, hLegG]) hCWH
    linarith only [hstep, hid, hgrow]
  have hdM : dataM ≤
      CdM * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep : CdM * (Real.sqrt shomM⁻¹ * Lg) ≤
        CdM * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM, hLegH]) hCdM
    linarith only [hdataM, hstep]
  -- the gradient half
  have hgrad1 : Real.sqrt shomM⁻¹ * dataG ≤ CdG * (Real.sqrt shomM⁻¹ * Lg) := by
    have hstep : Real.sqrt shomM⁻¹ * dataG ≤ Real.sqrt shomM⁻¹ * (CdG * Lg) :=
      mul_le_mul_of_nonneg_left hdataG hSI
    have hid : Real.sqrt shomM⁻¹ * (CdG * Lg) = CdG * (Real.sqrt shomM⁻¹ * Lg) := by
      ring
    linarith only [hstep, hid]
  have hhalf1 : gradM + Real.sqrt shomM⁻¹ * dataG ≤
      max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hpull := bracket_pull_weight (A := gradM) (L := Real.sqrt shomM⁻¹ * Lg)
      (W := CdG) hgradM hLegG
    have hmax : (1 : ℝ) ≤ max 1 CdG := le_max_left _ _
    have hgrow : max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg) ≤
        max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) :=
      mul_le_mul_of_nonneg_left (by linarith only [hLegH]) (by linarith only [hmax])
    linarith only [hgrad1, hpull, hgrow]
  -- the data half
  have hhalf2 : Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) +
        dataM ≤
      (Ccol * CWG + Ccol * CWH + CdM) *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep := mul_le_mul_of_nonneg_left
      (show Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H) ≤
          CWG * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) +
            CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) by
        linarith only [hoscG, hoscH]) hCcol
    have hexp : Ccol * (CWG * (gradM + Real.sqrt shomM⁻¹ * Lg +
            Real.sqrt shomM * Lh) +
          CWH * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)) +
        CdM * (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)
        = (Ccol * CWG + Ccol * CWH + CdM) *
          (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
    linarith only [hstep, hdM, hexp]
  -- the two halves, multiplied out
  have hbrNN : (0 : ℝ) ≤
      Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) + dataM := by
    have hb : (0 : ℝ) ≤ Ccol *
        (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) :=
      mul_nonneg hCcol (by
        have h1 : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ * (W * G) := mul_nonneg hSI hWG0
        have h2 : (0 : ℝ) ≤ Real.sqrt shomM * (W * H) := mul_nonneg hS hWH0
        linarith only [h1, h2])
    linarith only [hb, hdataM0]
  have hterm1 : Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG) ≤
      Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hstep := mul_le_mul_of_nonneg_left hhalf1 (mul_nonneg hKmain hR)
    calc Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG)
        ≤ Kmain * Real.rpow (3 : ℝ) E *
            (max 1 CdG *
              (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)) := hstep
      _ = Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
            (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
  have hterm2 : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
        (Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) +
          dataM) ≤
      Kdata * (Ccol * CWG + Ccol * CWH + CdM) * Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by
    have hexp : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) ≤
        Kdata * Real.rpow (3 : ℝ) E :=
      mul_le_mul_of_nonneg_left (rpow_three_threeQuarter_le hE) hKdata
    have hstep1 := mul_le_mul_of_nonneg_right hexp hbrNN
    have hstep2 := mul_le_mul_of_nonneg_left hhalf2 (mul_nonneg hKdata hR)
    calc Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
          (Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) + dataM)
        ≤ Kdata * Real.rpow (3 : ℝ) E *
            (Ccol * (Real.sqrt shomM⁻¹ * (W * G) + Real.sqrt shomM * (W * H)) +
              dataM) := hstep1
      _ ≤ Kdata * Real.rpow (3 : ℝ) E *
            ((Ccol * CWG + Ccol * CWH + CdM) *
              (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh)) := hstep2
      _ = Kdata * (Ccol * CWG + Ccol * CWH + CdM) * Real.rpow (3 : ℝ) E *
            (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
  have hsum : (Kmain * max 1 CdG + Kdata * (Ccol * CWG + Ccol * CWH + CdM)) *
        Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) =
      Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
          (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) +
        Kdata * (Ccol * CWG + Ccol * CWH + CdM) * Real.rpow (3 : ℝ) E *
          (gradM + Real.sqrt shomM⁻¹ * Lg + Real.sqrt shomM * Lh) := by ring
  linarith only [h, hterm1, hterm2, hsum, hT]

/-! ## 2. The `(W, G, H)` presentation that carries the boundary datum -/

/-- **The boundary presentation of the `dataOsc` slot.**

`RootClauseBArith.edFinalDataG_eq_dataOsc_scaled` puts the interior data leg in
the chain's slot at `H = 0` and `W = 4C_δC_gag/(1-r₁)`.  The boundary leg cannot
join that presentation without dividing by `W`, so the slot is entered at `W = 1`
instead, with the whole interior leg moved into `G`:

```text
   edFinalDataG + dataH_∂  =  1 · ( σ_m^{-1}·(σ_m·edFinalDataG)  +  dataH_∂ ) .
```

A ring identity modulo `σ_m·σ_m^{-1} = 1`. -/
theorem edFinalDataG_add_boundary_eq_dataOsc {M : ABKModel d} (Cdel Kg Cgag : ℝ)
    (m : ℤ) (H : ℝ) :
    edFinalDataG M Cdel (Kg * Cgag) m + H =
      1 * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
        ((Annealed.sigmaBar M m : ℝ) * edFinalDataG M Cdel (Kg * Cgag) m) + H) := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  rw [one_mul, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- **The `W·G` domination at the boundary presentation is an identity.**

`σ_m · edFinalDataG M C_δ (K_g C_gag) m = (4C_δC_gag/(1-r₁)) · 3^{m/2}K_g`:
the `σ_m^{-1}` of the Step-5 budget cancels against the `σ_m` introduced by
the presentation, leaving the printed datum `3^{m/2}K_g` at the budget's own
weight.  No estimate, no unit conversion. -/
theorem sigmaBar_mul_edFinalDataG_eq {M : ABKModel d} (Cdel Kg Cgag : ℝ) (m : ℤ) :
    (Annealed.sigmaBar M m : ℝ) * edFinalDataG M Cdel (Kg * Cgag) m =
      (edFinalDataOscW M Cdel * Cgag) * edFinalDataOscG Kg m := by
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).2
  have hpow : Real.rpow (3 : ℝ) ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := rfl
  rw [edFinalDataG, edFinalKgTop, edFinalDataOscW, edFinalDataOscG, hpow]
  field_simp

/-- The seam constant `C_WH = C_ah(1+C_gag)/(1-3^{-1/2}) + (4/log 3)·2C_bd`. -/
def boundaryCWH (d : ℕ) [NeZero d] (Cb C : ℝ) (k : ℕ) : ℝ :=
  edBoundaryCah d Cb C k * (1 + stepFourGagliardoConst d stepOneS) /
      (1 - stepFiveRatioH) +
    4 / Real.log 3 * (2 * edBoundaryCbd d Cb C k)

/-- **The unit-2 → unit-3 seam.**

```text
   dataH^print_∂ = ( C_ah(1+C_gag)/(1-3^{-1/2}) + (4/log 3)·2C_bd ) · 3^{m/2}K_h .
```

So the `hWH` slot of `rootClauseB_display_gate_boundaryC1` is met at that explicit
`C_WH`, with no estimate and no `σ`. -/
theorem edBoundaryDataHPrinted_eq_boundaryCWH_mul (d : ℕ) [NeZero d] (Cb C : ℝ)
    (k : ℕ) (Kh : ℝ) (m : ℤ) :
    edBoundaryDataHPrinted d Cb C k Kh m = boundaryCWH d Cb C k * edFinalDataOscG Kh m := by
  have hr : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have hpow : Real.rpow (3 : ℝ) ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := rfl
  rw [edBoundaryDataHPrinted, boundaryCWH, edFinalDataOscG, hpow]
  field_simp

/-- The seam constant is nonnegative. -/
theorem boundaryCWH_nonneg (d : ℕ) [NeZero d] (Cb : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (k : ℕ) : (0 : ℝ) ≤ boundaryCWH d Cb C k := by
  rw [boundaryCWH]
  have hlog : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hr : (0 : ℝ) < 1 - stepFiveRatioH := by linarith only [stepFiveRatioH_lt_one]
  have hgag : (0 : ℝ) ≤ stepFourGagliardoConst d stepOneS :=
    stepFourGagliardoConst_nonneg d stepOneS
  have h1 : (0 : ℝ) ≤ edBoundaryCah d Cb C k * (1 + stepFourGagliardoConst d stepOneS) /
      (1 - stepFiveRatioH) :=
    div_nonneg (mul_nonneg (edBoundaryCah_nonneg d Cb hC k) (by linarith only [hgag]))
      hr.le
  have h2 : (0 : ℝ) ≤ 4 / Real.log 3 * (2 * edBoundaryCbd d Cb C k) :=
    mul_nonneg (le_of_lt (div_pos (by norm_num) hlog))
      (by linarith only [edBoundaryCbd_nonneg d Cb hC k])
  linarith only [h1, h2]

end

end Algsuperdiff.Section4.Provider.Regularity
