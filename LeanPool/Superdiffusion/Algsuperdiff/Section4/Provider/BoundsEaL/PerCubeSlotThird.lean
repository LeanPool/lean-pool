/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeSlotCommon

/-!
# PerCubeSlotThird

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's third summand, evaluated at the anchor's scalar

## What this module does

`PerCubeFirstThird.exists_lintegral_rpow_step3ThirdTerm_le` supplies the third
summand's `q`-th moment at the SYMBOLIC majorant
`C ( σ_m^{-1} + R_{B5}(4q) )² R_{B6a}(4q)²`.  This module evaluates it:

```
( σ_m^{-1} + R_{B5}(4q) ) R_{B6a}(4q)  =  O( √q √γ ) ,
```

by bullet (B3) at BOTH `σ` indices (`PerCubeSlotCommon`), so the third
summand's majorant is `O(C q γ)` -- uniformly in the descendant scale, which is
exactly why Step 5 calls this summand straightforward.  The anchor's own first
slot `K p γ s^{-2}` dominates it, since `s ≤ 1/4`.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4 bullets (B3)/(B5)/(B6a), Step 5.
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
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Three arithmetic shorthands -/

theorem sqrt_four_eq_two : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

theorem sqrt_four_mul (q : ℝ) : Real.sqrt (4 * q) = 2 * Real.sqrt q := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) q, sqrt_four_eq_two]

theorem sqrt_mul_sqrt_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x * Real.sqrt y) ^ 2 = x * y := by
  rw [mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]

/-! ## 2. The regime bridge -/

/-- The anchor's own regime `γ ≤ C^{-10}` at the constant `C · c⋆^{-1}` IS the
Section-3 regime `γ ≤ C^{-10} c⋆^{10}`.  This is where the anchor's freedom to
choose its constant A `c⋆` (its binder order) is used. -/
theorem gamma_regime_of_cstar_scaled {C cst gam : ℝ}
    (h : gam ≤ ((C * cst⁻¹)⁻¹) ^ (10 : ℕ)) : gam ≤ (C⁻¹) ^ (10 : ℕ) * cst ^ (10 : ℕ) := by
  have hid : (C * cst⁻¹)⁻¹ = C⁻¹ * cst := by
    rw [mul_inv, inv_inv]
  rw [hid, mul_pow] at h
  exact h

/-! ## 3. The third summand at the anchor's first slot -/

/-- **The third summand, evaluated.**

`∫⁻ (step3ThirdTerm)^q ≤ (ofReal (C_d A q γ))^q`, uniformly in the descendant
scale.  The moment range hypothesis `8q ≤ γ^{-1}` is the anchor's own
`p ≤ C^{-1}γ^{-1}s` read at `q = p/2`; no other restriction on `p` is used. -/
theorem exists_lintegral_rpow_step3ThirdTerm_slot (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) :
    ∃ Creg A : ℝ, 0 < Creg ∧ 0 < A ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar →
        M.gamma ≤ (Creg⁻¹) ^ (10 : ℕ) → M.gamma ≤ 1 / 8 → ∀ Cd : ℝ, 0 ≤ Cd →
          ∀ (m : ℤ) (R : TriadicCube d), R.scale ≤ m → ∀ q : ℝ, 1 ≤ q →
            8 * q ≤ M.gamma⁻¹ →
              (∫⁻ omega : Cutoff.CutoffSample d,
                  ENNReal.ofReal (step3ThirdTerm Cd M m R omega
                    (lFreeGradSlot m (tailSeriesGauge m) R omega)) ^ q
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (Cd * A * (q * M.gamma)) ^ q := by
  classical
  obtain ⟨C3, hC36, hthird⟩ := exists_lintegral_rpow_step3ThirdTerm_le d
  obtain ⟨Cg, hCg0, hgaugeAll⟩ := exists_sigmaBar_gaugePackage d
  have hC30 : (0 : ℝ) < C3 := by linarith only [hC36]
  set Cmax : ℝ := max C3 Cg with hCmax
  have hCmax0 : (0 : ℝ) < Cmax := lt_of_lt_of_le hC30 (le_max_left _ _)
  set Y : ℝ := 8 * gammaMomentConst 2 * fullGradBound d * (Real.sqrt cstar)⁻¹ +
    2 * slotProductBound d cstar (C3 * cstar⁻¹) with hY
  have hE0 : (0 : ℝ) < C3 * cstar⁻¹ := mul_pos hC30 (inv_pos.mpr hcstar)
  have hY0 : (0 : ℝ) < Y := by
    have h1 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
    have h2 : (0 : ℝ) < fullGradBound d := fullGradBound_pos d
    have h3 : (0 : ℝ) < (Real.sqrt cstar)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hcstar)
    have h4 : (0 : ℝ) ≤ slotProductBound d cstar (C3 * cstar⁻¹) :=
      slotProductBound_nonneg d hE0
    rw [hY]
    have h5 : (0 : ℝ) < 8 * gammaMomentConst 2 * fullGradBound d * (Real.sqrt cstar)⁻¹ := by
      positivity
    linarith only [h4, h5]
  refine ⟨Cmax * cstar⁻¹, Y ^ 2, mul_pos hCmax0 (inv_pos.mpr hcstar),
    pow_pos hY0 2, ?_⟩
  intro M hcs hreg hgam Cd hCd m R hkm q hq h8q
  subst hcs
  have hcs0 : (0 : ℝ) < Disorder.cstar M := hcstar
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hginv : (0 : ℝ) < M.gamma⁻¹ := inv_pos.mpr hgam0
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hgam2 : M.gamma ≤ 1 / 2 := by linarith only [hgam]
  have hregC : M.gamma ≤ ((Cmax * (Disorder.cstar M)⁻¹)⁻¹) ^ (10 : ℕ) := hreg
  have hreg3 : M.gamma ≤ (C3⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    refine gamma_regime_of_cstar_scaled (le_trans hregC ?_)
    refine pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos hCmax0 (inv_pos.mpr hcs0)).le) ?_ 10
    exact inv_anti₀ (mul_pos hC30 (inv_pos.mpr hcs0))
      (mul_le_mul_of_nonneg_right (le_max_left C3 Cg) (inv_pos.mpr hcs0).le)
  have hregG : M.gamma ≤ (Cg⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    refine gamma_regime_of_cstar_scaled (le_trans hregC ?_)
    refine pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos hCmax0 (inv_pos.mpr hcs0)).le) ?_ 10
    exact inv_anti₀ (mul_pos hCg0 (inv_pos.mpr hcs0))
      (mul_le_mul_of_nonneg_right (le_max_right C3 Cg) (inv_pos.mpr hcs0).le)
  obtain ⟨hgB5, hgM, -, -⟩ := hgaugeAll M hregG
  refine le_trans (hthird M hreg3 Cd hCd m R hkm q hq) ?_
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hq0.le
  -- the real evaluation
  have h4q0 : (0 : ℝ) ≤ 4 * q := by linarith only [hq0]
  have h4qg : 4 * q ≤ M.gamma⁻¹ := by linarith only [h8q, hq0]
  have hsig0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M m).2.le
  have hlam0 : (0 : ℝ) ≤
      lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q) :=
    lambdaSlotMajorant_nonneg d M _ R.scale h4q0
  have hgrad0 : (0 : ℝ) ≤ gradSlotMajorant M R.scale (4 * q) :=
    gradSlotMajorant_nonneg M R.scale (4 * q)
  have hsq0 : (0 : ℝ) ≤ Real.sqrt q * Real.sqrt M.gamma :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- the (B5) leg
  have hleg2 : gradSlotMajorant M R.scale (4 * q) *
      lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q) ≤
      2 * slotProductBound d (Disorder.cstar M) (C3 * (Disorder.cstar M)⁻¹) *
        (Real.sqrt q * Real.sqrt M.gamma) := by
    refine le_trans (gradSlotMajorant_mul_lambdaSlotMajorant_le d M
      (mul_pos hC30 (inv_pos.mpr hcs0)) R.scale h4q0 h4qg hgam2 (hgB5 R.scale)) ?_
    rw [sqrt_four_mul]
    exact le_of_eq (by ring)
  -- the `σ_m^{-1}` leg
  have hgaugeM : (3 : ℝ) ^ (M.gamma * (R.scale : ℝ)) * ((Annealed.sigmaBar M m : ℝ))⁻¹ ≤
      4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hsig0) (hgM m)
    refine rpow_three_le_rpow_three ?_
    have hcast : (R.scale : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    exact mul_le_mul_of_nonneg_left hcast hgam0.le
  have hleg1 : ((Annealed.sigmaBar M m : ℝ))⁻¹ * gradSlotMajorant M R.scale (4 * q) ≤
      8 * gammaMomentConst 2 * fullGradBound d * (Real.sqrt (Disorder.cstar M))⁻¹ *
        (Real.sqrt q * Real.sqrt M.gamma) := by
    have hFG := fullGradConst_le M hgam2
    have hpre : (0 : ℝ) ≤ gammaMomentConst 2 * (2 * Real.sqrt q) :=
      mul_nonneg (gammaMomentConst_pos (by norm_num)).le (by positivity)
    have hid : ((Annealed.sigmaBar M m : ℝ))⁻¹ * gradSlotMajorant M R.scale (4 * q) =
        gammaMomentConst 2 * (2 * Real.sqrt q) * fullGradConst M *
          ((3 : ℝ) ^ (M.gamma * (R.scale : ℝ)) * ((Annealed.sigmaBar M m : ℝ))⁻¹) := by
      rw [gradSlotMajorant, gammaTwoMomentBound, sqrt_four_mul]
      simp only [rpowBridgeGauge]
      ring
    have hid2 : 8 * gammaMomentConst 2 * fullGradBound d *
        (Real.sqrt (Disorder.cstar M))⁻¹ * (Real.sqrt q * Real.sqrt M.gamma) =
        gammaMomentConst 2 * (2 * Real.sqrt q) * fullGradBound d *
          (4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) := by ring
    rw [hid, hid2]
    refine mul_le_mul (mul_le_mul_of_nonneg_left hFG hpre) hgaugeM ?_ ?_
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hsig0
    · exact mul_nonneg hpre (fullGradBound_pos d).le
  -- the combined linear bound, then the square
  have hlin : (((Annealed.sigmaBar M m : ℝ))⁻¹ +
      lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q)) *
      gradSlotMajorant M R.scale (4 * q) ≤
      (8 * gammaMomentConst 2 * fullGradBound d * (Real.sqrt (Disorder.cstar M))⁻¹ +
        2 * slotProductBound d (Disorder.cstar M) (C3 * (Disorder.cstar M)⁻¹)) *
        (Real.sqrt q * Real.sqrt M.gamma) := by
    have hexp : (((Annealed.sigmaBar M m : ℝ))⁻¹ +
        lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q)) *
        gradSlotMajorant M R.scale (4 * q) =
        ((Annealed.sigmaBar M m : ℝ))⁻¹ * gradSlotMajorant M R.scale (4 * q) +
          gradSlotMajorant M R.scale (4 * q) *
            lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q) := by ring
    rw [hexp, add_mul]
    exact add_le_add hleg1 hleg2
  have hlin0 : (0 : ℝ) ≤ (((Annealed.sigmaBar M m : ℝ))⁻¹ +
      lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q)) *
      gradSlotMajorant M R.scale (4 * q) :=
    mul_nonneg (by linarith only [hsig0, hlam0]) hgrad0
  have hsq := pow_le_pow_left₀ hlin0 hlin 2
  have hsqid : ((8 * gammaMomentConst 2 * fullGradBound d *
      (Real.sqrt (Disorder.cstar M))⁻¹ +
      2 * slotProductBound d (Disorder.cstar M) (C3 * (Disorder.cstar M)⁻¹)) *
      (Real.sqrt q * Real.sqrt M.gamma)) ^ 2 =
      (8 * gammaMomentConst 2 * fullGradBound d * (Real.sqrt (Disorder.cstar M))⁻¹ +
        2 * slotProductBound d (Disorder.cstar M) (C3 * (Disorder.cstar M)⁻¹)) ^ 2 *
        (q * M.gamma) := by
    rw [mul_pow, sqrt_mul_sqrt_sq hq0.le hgam0.le]
  have hlhsid : ((((Annealed.sigmaBar M m : ℝ))⁻¹ +
      lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q)) *
      gradSlotMajorant M R.scale (4 * q)) ^ 2 =
      (((Annealed.sigmaBar M m : ℝ))⁻¹ +
        lambdaSlotMajorant d M (C3 * (Disorder.cstar M)⁻¹) R.scale (4 * q)) ^ 2 *
        gradSlotMajorant M R.scale (4 * q) ^ 2 := by
    rw [mul_pow]
  rw [hsqid, hlhsid] at hsq
  have hfinal := mul_le_mul_of_nonneg_left hsq hCd
  have hid3 : Cd * (Y ^ 2 * (q * M.gamma)) = Cd * Y ^ 2 * (q * M.gamma) := by ring
  rw [hY] at hid3 ⊢
  linarith only [hfinal, hid3]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
