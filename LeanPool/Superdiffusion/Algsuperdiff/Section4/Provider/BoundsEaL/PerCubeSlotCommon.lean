/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeGaugeBounds

/-!
# PerCubeSlotCommon

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's per-cube evaluation: the shared slot bounds

## What this module supplies

Four evaluations shared by the three summands of Step 3's display:

* This is the one place where the two random slots become a `γ`-power: bullet
  (B3) at the (B5) index, exactly as `SigmaBarLandmark` records.
* `bracketMajorant_le` — hence the bracket majorant is `1 + O(1)` on the
  anchor's own range (`√(rγ) ≤ 1`, which `p ≤ C^{-1}γ^{-1}s` delivers).  This
  is the step that makes Step 5's bracket harmless at large `p`, and it is where
  the printed `q³e^{−C^{-1}γ^{-1}}` of bullet (B5)'s moment conversion is
  spent.
* `inv_sigmaBar_le_weight`, `lambdaSlotMajorant_le_weight` — the two `σ`-gauges
  with the `3^{γ·}` weight moved to the other side, which is how the per-scale
  factor `3^{γ(m−j)}` of Step 5's geometric sum is produced.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4, Step 5.
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular

noncomputable section

variable {d : ℕ}

/-! ## 1. The product of bullets (B6a) and (B5) -/

/-- The constant of the `(B6a)·(B5)` product: `16 C(2) · fullGradBound ·
c⋆^{-1/2} · lambdaSlotFactorBound`. -/
def slotProductBound (d : ℕ) (cst E : ℝ) : ℝ :=
  16 * gammaMomentConst 2 * fullGradBound d * (Real.sqrt cst)⁻¹ *
    lambdaSlotFactorBound d E

theorem slotProductBound_nonneg (d : ℕ) {cst E : ℝ} (hE : 0 < E) :
    0 ≤ slotProductBound d cst E := by
  have h1 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have h2 : (0 : ℝ) < fullGradBound d := fullGradBound_pos d
  have h3 : (0 : ℝ) ≤ (Real.sqrt cst)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h4 : (0 : ℝ) < lambdaSlotFactorBound d E := lambdaSlotFactorBound_pos d hE
  rw [slotProductBound]
  positivity

/-- **THE `(B6a)·(B5)` IS `O(√r √γ)`.**

The `3^{γj}` of bullet (B6a) meets the `σ_{j−1}^{-1}` of bullet (B5), and (B3)
at that index turns the pair into `16 c⋆^{-1/2} √γ`. -/
theorem gradSlotMajorant_mul_lambdaSlotMajorant_le (d : ℕ) (M : ABKModel d) {E : ℝ}
    (hE : 0 < E) (j : ℤ) {r : ℝ} (hr : 0 ≤ r) (hrg : r ≤ M.gamma⁻¹)
    (hgam : M.gamma ≤ 1 / 2)
    (hgauge : (3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤
      16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) :
    gradSlotMajorant M j r * lambdaSlotMajorant d M E j r ≤
      slotProductBound d (Disorder.cstar M) E * (Real.sqrt r * Real.sqrt M.gamma) := by
  have hFG := fullGradConst_le M hgam
  have hF := lambdaSlotFactor_le d M hE hr hrg
  have hFG0 : (0 : ℝ) ≤ fullGradConst M := (fullGradConst_pos M).le
  have hF0 : (0 : ℝ) ≤ lambdaSlotFactor d M E r := by
    have h1 : (0 : ℝ) ≤ lambdaUpscaleConst d * Support.cgEllipLowerConstant d :=
      mul_nonneg (lambdaUpscaleConst_pos d).le (Support.cgEllipLowerConstant_pos d).le
    have h2 : (0 : ℝ) ≤ gammaMomentConst (1 / 3) * r ^ ((1 / 3 : ℝ))⁻¹ *
        (lambdaUpscaleConst d * lambdaMaxOrliczConst d * Proportion.cgTailScale M E) := by
      refine mul_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le
        (Real.rpow_nonneg hr _)) ?_
      exact mul_nonneg (mul_nonneg (lambdaUpscaleConst_pos d).le
        (lambdaMaxOrliczConst_pos d).le) (Proportion.cgTailScale_pos M E).le
    rw [lambdaSlotFactor]
    linarith only [h1, h2]
  have hgauge0 : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (j : ℝ)) *
      ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (inv_nonneg.mpr (Annealed.sigmaBar M (j - 1)).2.le)
  have hpre : (0 : ℝ) ≤ gammaMomentConst 2 * Real.sqrt r :=
    mul_nonneg (gammaMomentConst_pos (by norm_num)).le (Real.sqrt_nonneg _)
  have hprod : fullGradConst M * lambdaSlotFactor d M E r ≤
      fullGradBound d * lambdaSlotFactorBound d E :=
    mul_le_mul hFG hF hF0 (fullGradBound_pos d).le
  have hprod0 : (0 : ℝ) ≤ fullGradBound d * lambdaSlotFactorBound d E :=
    mul_nonneg (fullGradBound_pos d).le (lambdaSlotFactorBound_pos d hE).le
  have hid : gradSlotMajorant M j r * lambdaSlotMajorant d M E j r =
      gammaMomentConst 2 * Real.sqrt r * (fullGradConst M * lambdaSlotFactor d M E r) *
        ((3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹) := by
    rw [gradSlotMajorant, gammaTwoMomentBound, lambdaSlotMajorant_eq_mul]
    simp only [rpowBridgeGauge]
    ring
  have hid2 : slotProductBound d (Disorder.cstar M) E *
      (Real.sqrt r * Real.sqrt M.gamma) =
      gammaMomentConst 2 * Real.sqrt r * (fullGradBound d * lambdaSlotFactorBound d E) *
        (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) := by
    rw [slotProductBound]
    ring
  rw [hid, hid2]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hprod hpre) hgauge hgauge0
    (mul_nonneg hpre hprod0)

/-! ## 2. The bracket majorant is bounded -/

/-- **The bracket is `O(1)` at large `p`.**

On the anchor's own range -- `2r ≤ γ^{-1}`, which `p ≤ C^{-1}γ^{-1}s` delivers
at every exponent Step 5 uses -- the bracket majorant is at most `1 +
slotProductBound`. -/
theorem bracketMajorant_le (d : ℕ) (M : ABKModel d) {E : ℝ} (hE : 0 < E) (j : ℤ)
    {r : ℝ} (hr : 0 ≤ r) (hrg : 2 * r ≤ M.gamma⁻¹) (hgam : M.gamma ≤ 1 / 2)
    (hgauge : (3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤
      16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) :
    bracketMajorant d M E j r ≤ 1 + slotProductBound d (Disorder.cstar M) E := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have h2r : (0 : ℝ) ≤ 2 * r := by linarith only [hr]
  have hbase := gradSlotMajorant_mul_lambdaSlotMajorant_le d M hE j h2r hrg hgam hgauge
  have hprodg : 2 * r * M.gamma ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hrg hgam0.le
    rw [inv_mul_cancel₀ (ne_of_gt hgam0)] at h
    exact h
  have hsqrt : Real.sqrt (2 * r) * Real.sqrt M.gamma ≤ 1 := by
    rw [← Real.sqrt_mul h2r]
    have h := Real.sqrt_le_sqrt hprodg
    rwa [Real.sqrt_one] at h
  have hstep := mul_le_mul_of_nonneg_left hsqrt
    (slotProductBound_nonneg d (cst := Disorder.cstar M) hE)
  rw [bracketMajorant]
  have hchain : gradSlotMajorant M j (2 * r) * lambdaSlotMajorant d M E j (2 * r) ≤
      slotProductBound d (Disorder.cstar M) E := by
    refine le_trans hbase ?_
    rw [mul_one] at hstep
    exact hstep
  linarith only [hchain]

/-! ## 3. The two gauges, with the weight inverted -/

/-- `σ_m^{-1} ≤ 3^{−γm} · 4 c⋆^{-1/2}√γ`. -/
theorem inv_sigmaBar_le_weight (M : ABKModel d) (m : ℤ)
    (hgauge : (3 : ℝ) ^ (M.gamma * (m : ℝ)) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
      4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) :
    ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
      (3 : ℝ) ^ (-(M.gamma * (m : ℝ))) *
        (4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) :=
  le_rpow_neg_mul_of_rpow_mul_le hgauge

/-- `Λ_{(B5)}(r) ≤ 3^{−γj} · 16 c⋆^{-1/2}√γ · lambdaSlotFactorBound`. -/
theorem lambdaSlotMajorant_le_weight (d : ℕ) (M : ABKModel d) {E : ℝ} (hE : 0 < E) (j : ℤ)
    {r : ℝ} (hr : 0 ≤ r) (hrg : r ≤ M.gamma⁻¹)
    (hgauge : (3 : ℝ) ^ (M.gamma * (j : ℝ)) * ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ ≤
      16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) :
    lambdaSlotMajorant d M E j r ≤
      (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) *
        (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) *
          lambdaSlotFactorBound d E) := by
  have hinv := le_rpow_neg_mul_of_rpow_mul_le hgauge
  have hF := lambdaSlotFactor_le d M hE hr hrg
  have hF0 : (0 : ℝ) ≤ lambdaSlotFactor d M E r := by
    have h1 : (0 : ℝ) ≤ lambdaUpscaleConst d * Support.cgEllipLowerConstant d :=
      mul_nonneg (lambdaUpscaleConst_pos d).le (Support.cgEllipLowerConstant_pos d).le
    have h2 : (0 : ℝ) ≤ gammaMomentConst (1 / 3) * r ^ ((1 / 3 : ℝ))⁻¹ *
        (lambdaUpscaleConst d * lambdaMaxOrliczConst d * Proportion.cgTailScale M E) := by
      refine mul_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le
        (Real.rpow_nonneg hr _)) ?_
      exact mul_nonneg (mul_nonneg (lambdaUpscaleConst_pos d).le
        (lambdaMaxOrliczConst_pos d).le) (Proportion.cgTailScale_pos M E).le
    rw [lambdaSlotFactor]
    linarith only [h1, h2]
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) *
      (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) := by
    refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
    exact mul_nonneg (by norm_num)
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hsig0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (j - 1) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (j - 1)).2.le
  rw [lambdaSlotMajorant_eq_mul]
  have hstep := mul_le_mul hinv hF hF0 hw0
  have hid : (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) *
      (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) *
      lambdaSlotFactorBound d E =
      (3 : ℝ) ^ (-(M.gamma * (j : ℝ))) *
        (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) *
          lambdaSlotFactorBound d E) := by ring
  linarith only [hstep, hid, hsig0]

/-! ## 4. The squared value slot -/

/-- The dimensional width of the value slot: the `L∞` leg's constant plus the
mean-value tail's. -/
def valueSlotWidth (d : ℕ) : ℝ := valueLinftyConst d + centeringConst d * deepGradBound

theorem valueSlotWidth_pos {d : ℕ} (hd : 0 < d) : 0 < valueSlotWidth d := by
  have h1 : (0 : ℝ) < valueLinftyConst d := valueLinftyConst_pos hd
  have h2 : (0 : ℝ) ≤ centeringConst d := centeringConst_nonneg d
  have h3 : (0 : ℝ) < deepGradBound := deepGradBound_pos
  rw [valueSlotWidth]
  positivity

/-- **The squared value slot.** -/
theorem valueSlotMajorant_sq_le (M : ABKModel d) (m j : ℤ) {r : ℝ} (hr : 0 ≤ r)
    (hgam : M.gamma ≤ 1 / 2) (ht : 0 ≤ (m : ℝ) - (j : ℝ)) :
    valueSlotMajorant M m j r ^ 2 ≤
      2 * (gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2) *
        (r * (1 + ((m : ℝ) - (j : ℝ)))) * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := by
  have hmin0 : (0 : ℝ) ≤ min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ))) :=
    le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hC2 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (m : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hDG := deepGradConst_le M hgam
  have hcc : (0 : ℝ) ≤ centeringConst d := centeringConst_nonneg d
  -- the linear bound
  have hlin : valueSlotMajorant M m j r ≤
      gammaMomentConst 2 * Real.sqrt r * valueSlotWidth d *
        (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    have hpre : (0 : ℝ) ≤ gammaMomentConst 2 * Real.sqrt r :=
      mul_nonneg hC2.le (Real.sqrt_nonneg _)
    have hstep : centeringConst d * deepGradConst M ≤
        centeringConst d * deepGradBound * (1 + min (Real.sqrt M.gamma⁻¹)
          (Real.sqrt ((m : ℝ) - (j : ℝ)))) := by
      have h1 : centeringConst d * deepGradConst M ≤ centeringConst d * deepGradBound :=
        mul_le_mul_of_nonneg_left hDG hcc
      have h2 : (0 : ℝ) ≤ centeringConst d * deepGradBound :=
        mul_nonneg hcc deepGradBound_pos.le
      have h3 := mul_le_mul_of_nonneg_left (by linarith only [hmin0] :
        (1 : ℝ) ≤ 1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) h2
      linarith only [h1, h3]
    have hinner : valueLinftyConst d *
          (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) +
        centeringConst d * deepGradConst M ≤
        valueSlotWidth d *
          (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) := by
      rw [valueSlotWidth]
      linarith only [hstep]
    have hmul := mul_le_mul_of_nonneg_right hinner hw
    have hleft : valueSlotMajorant M m j r =
        gammaMomentConst 2 * Real.sqrt r *
          ((valueLinftyConst d *
              (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) +
            centeringConst d * deepGradConst M) * (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by
      rw [valueSlotMajorant, gammaTwoMomentBound, gammaTwoMomentBound]
      simp only [rpowBridgeGauge]
      ring
    have hright : gammaMomentConst 2 * Real.sqrt r * valueSlotWidth d *
        (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) *
        (3 : ℝ) ^ (M.gamma * (m : ℝ)) =
        gammaMomentConst 2 * Real.sqrt r *
          ((valueSlotWidth d *
            (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ))))) *
            (3 : ℝ) ^ (M.gamma * (m : ℝ))) := by ring
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left hmul hpre
  -- the square
  have hlhs0 : (0 : ℝ) ≤ valueSlotMajorant M m j r := valueSlotMajorant_nonneg M m j r
  have hsq := pow_le_pow_left₀ hlhs0 hlin 2
  have hminsq := one_add_min_sqrt_sq_le (a := M.gamma⁻¹) (b := (m : ℝ) - (j : ℝ)) ht
  have hsqrtr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  have hweight : ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
      (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (m : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring_nf
  have hexpand : (gammaMomentConst 2 * Real.sqrt r * valueSlotWidth d *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) *
      (3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 =
      gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * Real.sqrt r ^ 2 *
        (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) ^ 2 *
        ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ 2 := by ring
  have hcoef : (0 : ℝ) ≤ gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * r :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hr
  have hfin : gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * r *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) ^ 2 ≤
      gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * r *
        (2 * (1 + ((m : ℝ) - (j : ℝ)))) := mul_le_mul_of_nonneg_left hminsq hcoef
  have hweight0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hfin2 := mul_le_mul_of_nonneg_right hfin hweight0
  rw [hexpand, hsqrtr, hweight] at hsq
  have hid : gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * r *
      (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) ^ 2 *
      (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) =
      gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * r *
        (1 + min (Real.sqrt M.gamma⁻¹) (Real.sqrt ((m : ℝ) - (j : ℝ)))) ^ 2 *
        (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := rfl
  have hid2 : gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2 * r *
      (2 * (1 + ((m : ℝ) - (j : ℝ)))) * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) =
      2 * (gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2) *
        (r * (1 + ((m : ℝ) - (j : ℝ)))) * (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))) := by ring
  linarith only [hsq, hfin2, hid, hid2]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
