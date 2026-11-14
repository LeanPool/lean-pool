/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootAssemblyChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSixInteriorEndpoint

/-!
# RootClauseBArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Item (i): the origin cube's scale factor -/

/-- **Item (i)**: the chain's `oscHi` normalization `(cubeScaleFactor □_k)⁻¹` IS
the `3^{-k}` that's `e.oscillation.Holder.bound` prints. -/
theorem cubeScaleFactor_originCube_inv (d : ℕ) (k : ℤ) :
    (cubeScaleFactor (originCube d k))⁻¹ = (3 : ℝ) ^ (-k) := by
  rw [cubeScaleFactor, zpow_neg]
  rfl

/-! ## 2. Item (ii): the `dataOsc` presentation -/

/-- **The `dataOsc` weight** `W = 4C_δ/(1 - r₁)` of the interior Step-5 budget. -/
def edFinalDataOscW (M : ABKModel d) (Cdel : ℝ) : ℝ :=
  4 * Cdel / (1 - stepFiveRatioG M)

/-- **The `dataOsc` top-scale datum** `G = 3^{m/2}K_g`. -/
def edFinalDataOscG (Kg : ℝ) (m : ℤ) : ℝ :=
  Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg

theorem edFinalDataOscW_nonneg {M : ABKModel d} (hgamma : M.gamma < 1 / 2)
    {Cdel : ℝ} (hC : 0 ≤ Cdel) : 0 ≤ edFinalDataOscW M Cdel := by
  have h1 : (0 : ℝ) < 1 - stepFiveRatioG M := by
    linarith only [stepFiveRatioG_lt_one hgamma]
  exact div_nonneg (by linarith only [hC]) h1.le

theorem edFinalDataOscG_nonneg {Kg : ℝ} (hKg : 0 ≤ Kg) (m : ℤ) :
    0 ≤ edFinalDataOscG Kg m :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _) hKg

/-- **Item (ii)'s own argument.**  The Step-6 interior endpoint states its data leg
as `edFinalDataG M C_δ (K_g·C_{S4.4}) m + 0`, so the chain's `dataOsc` slot is
met at the weight `W = (4C_δ/(1-r₁))·C_{S4.4}` and the printed datum `G =
3^{m/2}K_g` — the Gagliardo constant joins the W, not the leg, which is what
puts the root's own `3^{m/2}K_g` in the bracket.  A ring identity. -/
theorem edFinalDataG_eq_dataOsc_scaled (M : ABKModel d) (Cdel Kg Cgag : ℝ) (m : ℤ) :
    edFinalDataG M Cdel (Kg * Cgag) m + 0 =
      (edFinalDataOscW M Cdel * Cgag) *
        (((Annealed.sigmaBar M m : ℝ))⁻¹ * edFinalDataOscG Kg m + 0) := by
  have hpow : Real.rpow (3 : ℝ) ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := rfl
  rw [edFinalDataG, edFinalKgTop, edFinalDataOscW, edFinalDataOscG, hpow]
  ring

/-! ## 3. Item (iv): the outer collapse onto the root's two legs -/

/-- Pulling the interior budget's constant `W` out of the data leg: the printed
bracket carries `√σ_m^{-1}·3^{m/2}K_g` with NO `W`, so `W` must join the
prefactor.  Abstract reals. -/
theorem bracket_pull_weight {A L W : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    A + W * L ≤ max 1 W * (A + L) := by
  have h1 : (1 : ℝ) ≤ max 1 W := le_max_left _ _
  have h2 : W ≤ max 1 W := le_max_right _ _
  have hA' : A ≤ max 1 W * A := by
    have := mul_le_mul_of_nonneg_right h1 hA
    linarith only [this]
  have hL' : W * L ≤ max 1 W * L := mul_le_mul_of_nonneg_right h2 hL
  have hexp : max 1 W * (A + L) = max 1 W * A + max 1 W * L := by ring
  linarith only [hA', hL', hexp]

/-- **Item (iv): the clause-(B) bracket collapse.**

's outer collapse in the shape the concrete carriers need.  The Step-7 end
chain concludes

```text
  gradLoc ≤ Kmain·3^E·(gradM + √σ_m^{-1}·dataG)
          + Kdata·3^{3E/4}·(Ccol·(W·((√σ_m)^{-1}·G + √σ_m·H)) + dataM) ,
```

with `H = 0` on the interior branch,
and `e.energy.density.estimate` prints ONE power of three and the SINGLE data
leg `Lg = 3^{m/2}K_g`.  Three DOMINATIONS collapse the former onto the latter —
the Poincaré-leg datum (`dataG ≤ CdG·Lg`), the oscillation-leg datum (`W·G
≤·Lg`) and the Caccioppoli's own data leg (`dataM ≤ CdM·√σ_m^{-1}·Lg`) —
together with the parent's own exponent step `3^{3E/4} ≤ 3^E`
(`RootAssemblyChain.rpow_three_threeQuarter_le`).

Pure arithmetic: every domination is a hypothesis, `Real.rpow` is opaque
throughout, and no estimate is derived. -/
theorem rootClauseB_collapse
    {E Kmain Kdata Ccol CdG CWG CdM shomM gradLoc gradM dataG dataM W G Lg : ℝ}
    (hKmain : 0 ≤ Kmain) (hKdata : 0 ≤ Kdata) (hCcol : 0 ≤ Ccol)
    (hCWG : 0 ≤ CWG) (hCdM : 0 ≤ CdM) (hE : 0 ≤ E) (hgradM : 0 ≤ gradM) (hLg : 0 ≤ Lg)
    (hWG0 : 0 ≤ W * G) (hdataM0 : 0 ≤ dataM)
    (hdataG : dataG ≤ CdG * Lg)
    (hWG : W * G ≤ CWG * Lg)
    (hdataM : dataM ≤ CdM * (Real.sqrt shomM⁻¹ * Lg))
    (h : gradLoc ≤
      Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG) +
        Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
          (Ccol *
            (W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * 0)) + dataM)) :
    gradLoc ≤
      (Kmain * max 1 CdG + Kdata * (Ccol * CWG + CdM)) *
        Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * Lg) := by
  have hSI : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ := Real.sqrt_nonneg _
  have hinv : (Real.sqrt shomM)⁻¹ = Real.sqrt shomM⁻¹ := (Real.sqrt_inv shomM).symm
  have hR : (0 : ℝ) ≤ Real.rpow (3 : ℝ) E := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hLeg : (0 : ℝ) ≤ Real.sqrt shomM⁻¹ * Lg := mul_nonneg hSI hLg
  have hTot : (0 : ℝ) ≤ gradM + Real.sqrt shomM⁻¹ * Lg := by
    linarith only [hgradM, hLeg]
  -- the data bracket, rewritten with `H = 0` and the two square roots identified
  have hbr : W * ((Real.sqrt shomM)⁻¹ * G + Real.sqrt shomM * 0) =
      Real.sqrt shomM⁻¹ * (W * G) := by
    rw [hinv]; ring
  rw [hbr] at h
  -- the oscillation half
  have hosc1 : Real.sqrt shomM⁻¹ * (W * G) ≤ CWG * (Real.sqrt shomM⁻¹ * Lg) := by
    have hstep : Real.sqrt shomM⁻¹ * (W * G) ≤ Real.sqrt shomM⁻¹ * (CWG * Lg) :=
      mul_le_mul_of_nonneg_left hWG hSI
    calc Real.sqrt shomM⁻¹ * (W * G) ≤ Real.sqrt shomM⁻¹ * (CWG * Lg) := hstep
      _ = CWG * (Real.sqrt shomM⁻¹ * Lg) := by ring
  have hhalf2 : Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM ≤
      (Ccol * CWG + CdM) * (gradM + Real.sqrt shomM⁻¹ * Lg) := by
    have h1 : Ccol * (Real.sqrt shomM⁻¹ * (W * G)) ≤
        (Ccol * CWG) * (Real.sqrt shomM⁻¹ * Lg) := by
      have := mul_le_mul_of_nonneg_left hosc1 hCcol
      calc Ccol * (Real.sqrt shomM⁻¹ * (W * G))
          ≤ Ccol * (CWG * (Real.sqrt shomM⁻¹ * Lg)) := this
        _ = (Ccol * CWG) * (Real.sqrt shomM⁻¹ * Lg) := by ring
    have h2 : (Ccol * CWG) * (Real.sqrt shomM⁻¹ * Lg) ≤
        (Ccol * CWG) * (gradM + Real.sqrt shomM⁻¹ * Lg) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM])
        (mul_nonneg hCcol hCWG)
    have h3 : CdM * (Real.sqrt shomM⁻¹ * Lg) ≤
        CdM * (gradM + Real.sqrt shomM⁻¹ * Lg) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgradM]) hCdM
    have hexp : (Ccol * CWG + CdM) * (gradM + Real.sqrt shomM⁻¹ * Lg) =
        (Ccol * CWG) * (gradM + Real.sqrt shomM⁻¹ * Lg) +
          CdM * (gradM + Real.sqrt shomM⁻¹ * Lg) := by ring
    linarith only [h1, h2, h3, hdataM, hexp]
  -- the gradient half
  have hgrad1 : Real.sqrt shomM⁻¹ * dataG ≤ CdG * (Real.sqrt shomM⁻¹ * Lg) := by
    have hstep : Real.sqrt shomM⁻¹ * dataG ≤ Real.sqrt shomM⁻¹ * (CdG * Lg) :=
      mul_le_mul_of_nonneg_left hdataG hSI
    calc Real.sqrt shomM⁻¹ * dataG ≤ Real.sqrt shomM⁻¹ * (CdG * Lg) := hstep
      _ = CdG * (Real.sqrt shomM⁻¹ * Lg) := by ring
  have hhalf1 : gradM + Real.sqrt shomM⁻¹ * dataG ≤
      max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg) := by
    have hpull := bracket_pull_weight (A := gradM) (L := Real.sqrt shomM⁻¹ * Lg)
      (W := CdG) hgradM hLeg
    linarith only [hgrad1, hpull]
  -- the two halves, multiplied out
  have hterm1 : Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG) ≤
      Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg) := by
    have hstep := mul_le_mul_of_nonneg_left hhalf1 (mul_nonneg hKmain hR)
    calc Kmain * Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * dataG)
        ≤ Kmain * Real.rpow (3 : ℝ) E *
            (max 1 CdG * (gradM + Real.sqrt shomM⁻¹ * Lg)) := hstep
      _ = Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
            (gradM + Real.sqrt shomM⁻¹ * Lg) := by ring
  have hbrNN : (0 : ℝ) ≤ Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM := by
    have h1 : (0 : ℝ) ≤ Ccol * (Real.sqrt shomM⁻¹ * (W * G)) :=
      mul_nonneg hCcol (mul_nonneg hSI hWG0)
    linarith only [h1, hdataM0]
  have hterm2 : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
        (Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM) ≤
      Kdata * (Ccol * CWG + CdM) * Real.rpow (3 : ℝ) E *
        (gradM + Real.sqrt shomM⁻¹ * Lg) := by
    have hexp : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) ≤
        Kdata * Real.rpow (3 : ℝ) E :=
      mul_le_mul_of_nonneg_left (rpow_three_threeQuarter_le hE) hKdata
    have hstep1 : Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
        (Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM) ≤
        Kdata * Real.rpow (3 : ℝ) E *
          (Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM) :=
      mul_le_mul_of_nonneg_right hexp hbrNN
    have hstep2 := mul_le_mul_of_nonneg_left hhalf2 (mul_nonneg hKdata hR)
    calc Kdata * Real.rpow (3 : ℝ) (3 / 4 * E) *
          (Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM)
        ≤ Kdata * Real.rpow (3 : ℝ) E *
            (Ccol * (Real.sqrt shomM⁻¹ * (W * G)) + dataM) := hstep1
      _ ≤ Kdata * Real.rpow (3 : ℝ) E *
            ((Ccol * CWG + CdM) * (gradM + Real.sqrt shomM⁻¹ * Lg)) := hstep2
      _ = Kdata * (Ccol * CWG + CdM) * Real.rpow (3 : ℝ) E *
            (gradM + Real.sqrt shomM⁻¹ * Lg) := by ring
  have hsum : (Kmain * max 1 CdG + Kdata * (Ccol * CWG + CdM)) *
        Real.rpow (3 : ℝ) E * (gradM + Real.sqrt shomM⁻¹ * Lg) =
      Kmain * max 1 CdG * Real.rpow (3 : ℝ) E *
          (gradM + Real.sqrt shomM⁻¹ * Lg) +
        Kdata * (Ccol * CWG + CdM) * Real.rpow (3 : ℝ) E *
          (gradM + Real.sqrt shomM⁻¹ * Lg) := by ring
  linarith only [h, hterm1, hterm2, hsum, hTot]

end

end Algsuperdiff.Section4.Provider.Regularity
