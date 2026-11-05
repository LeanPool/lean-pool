/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.PerCubeSlotFirst

/-!
# PerCubeSlotSecond

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 5's second summand, evaluated at the anchor's scalar

## What this module does

`SecondTermMoment.exists_lintegral_rpow_step3SecondTerm_le` supplies the second
summand's `q`-th moment at a symbolic majorant with two legs.  This module
evaluates both against the anchor's own linear and flat per-scale slots
`K p γ(m−j) 3^{2γ(m−j)}` and `K p γ 3^{2γ(m−j)}`:

* **the value leg** is `σ_m^{-1} · R_{B5}(2q) · R_bracket(4q) · R_{B6b}(8q)²`.
  The two `σ`-gauges contribute `3^{−γm}` and `3^{−γj}`, each with a `√γ`, and
  the squared value slot contributes `3^{2γm}` and `q(1+(m−j))`; the three
  weights combine to the per-scale `3^{γ(m−j)}` of Step 5's geometric sum
  (`SecondTermArithmetic.rpow_three_gauge_triple`), and the two `√γ` to the
  anchor's `γ`.
* **the (B2) leg** is deterministic apart from `R_{B5}(2q) R_bracket(2q)`, and
  its scalar `σ_m^{-1}σ_{j−2}²(σ_mσ_{j−2}^{-1}−1)²` is bullet (B1) twice
  against bullet (B2).  (B2)'s squared minimum splits into the same two slots
  by `SecondTermArithmetic.min_one_add_sq_le`, and its `γ^{3/5}|log γ|²`
  portion is `O(√γ)` only A squaring -- which is what
  `SecondTermArithmetic.gammaLogPortion_sq_le` supplies.

## References

* ABK26, `l.bounds.mathcal.E.aL`, Step 4 bullets (B1)/(B2)/(B5)/(B6b), Step 5
  (in particular the `j`-sum).
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

/-! ## 1. A four-factor product step -/

/-- Four nonnegative factors, bounded one by one. -/
private theorem mulLeMul4 {a b c e A B C E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (he : 0 ≤ e) (hA : a ≤ A) (hB : b ≤ B) (hC : c ≤ C) (hE : e ≤ E) :
    a * (b * (c * e)) ≤ A * (B * (C * E)) := by
  have hCE : c * e ≤ C * E := mul_le_mul hC hE he (le_trans hc hC)
  have hce0 : (0 : ℝ) ≤ c * e := mul_nonneg hc he
  have hBCE : b * (c * e) ≤ B * (C * E) := mul_le_mul hB hCE hce0 (le_trans hb hB)
  exact mul_le_mul hA hBCE (mul_nonneg hb hce0) (le_trans ha hA)

/-! ## 2. Bullet (B2)'s squared minimum, split into the two slots -/

/-- **Bullet (B2)'s squared minimum, split.**

`(min{1, γ(t+2) + γ^{3/5}|log γ|²})² ≤ 320004 (γt + γ)`: the linear and flat
per-scale shapes, at both branches of the minimum at once.  The `320000` is `2·400²`, the
square of the scale-free log bound `γ^{1/10}(log γ)² ≤ 400`. -/
theorem sigmaBarContinuity_min_sq_le {g t : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) (ht : 0 ≤ t) :
    (min 1 (g * (t + 2) + g ^ ((3 : ℝ) / 5) * |Real.log g| ^ 2)) ^ 2 ≤
      320004 * (g * t + g) := by
  have ha0 : (0 : ℝ) ≤ g * (t + 2) := mul_nonneg hg0.le (by linarith only [ht])
  have hb0 : (0 : ℝ) ≤ g ^ ((3 : ℝ) / 5) * |Real.log g| ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hg0.le _) (sq_nonneg _)
  have hmin := min_one_add_sq_le ha0 hb0
  have hlog := gammaLogPortion_sq_le hg0 hg1
  have hid : g * (t + 2) = g * t + 2 * g := by ring
  have hgt : (0 : ℝ) ≤ g * t := mul_nonneg hg0.le ht
  linarith only [hmin, hlog, hid, hgt]

/-! ## 3. The two leg constants -/

/-- The constant of the second summand's VALUE leg. -/
def secondValueLegBound (d : ℕ) (cst EL EB : ℝ) : ℝ :=
  4 * ((Real.sqrt cst)⁻¹ * (Real.sqrt cst)⁻¹) * (16 * lambdaSlotFactorBound d EL) *
    ((1 + slotProductBound d cst EB) *
      (8 * (2 * (gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2))))

/-- The constant of the second summand's (B2) leg. -/
def secondRatioLegBound (d : ℕ) (cst EL EB C2b : ℝ) : ℝ :=
  4 * 4 * lambdaSlotFactorBound d EL *
    ((1 + slotProductBound d cst EB) * (C2b * 320004))

theorem secondValueLegBound_pos (d : ℕ) (hd : 0 < d) {cst EL EB : ℝ} (hcst : 0 < cst)
    (hEL : 0 < EL) (hEB : 0 < EB) : 0 < secondValueLegBound d cst EL EB := by
  have h1 : (0 : ℝ) < (Real.sqrt cst)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hcst)
  have h2 : (0 : ℝ) < lambdaSlotFactorBound d EL := lambdaSlotFactorBound_pos d hEL
  have h3 : (0 : ℝ) ≤ slotProductBound d cst EB := slotProductBound_nonneg d hEB
  have h4 : (0 : ℝ) < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have h5 : (0 : ℝ) < valueSlotWidth d := valueSlotWidth_pos hd
  have h6 : (0 : ℝ) < 1 + slotProductBound d cst EB := by linarith only [h3]
  rw [secondValueLegBound]
  positivity

theorem secondRatioLegBound_pos (d : ℕ) {cst EL EB C2b : ℝ} (hEL : 0 < EL) (hEB : 0 < EB)
    (hC2b : 0 < C2b) : 0 < secondRatioLegBound d cst EL EB C2b := by
  have h2 : (0 : ℝ) < lambdaSlotFactorBound d EL := lambdaSlotFactorBound_pos d hEL
  have h3 : (0 : ℝ) ≤ slotProductBound d cst EB := slotProductBound_nonneg d hEB
  have h6 : (0 : ℝ) < 1 + slotProductBound d cst EB := by linarith only [h3]
  rw [secondRatioLegBound]
  positivity

/-! ## 4. The second summand at the anchor's linear and flat slots -/

private theorem stepThreeSecondTerm_diffusivityRatioBound :
    ∀ (d : ℕ) (CL CB C2b : ℝ),
      (0 : ℝ) < C2b →
        ∀ (M : ABKModel d) (m : ℤ) (R : TriadicCube d) (q : ℝ),
          (1 : ℝ) ≤ q →
            (0 : ℝ) < CL * (Disorder.cstar M)⁻¹ →
              (0 : ℝ) < CB * (Disorder.cstar M)⁻¹ →
                (0 : ℝ) < M.gamma →
                  (0 : ℝ) ≤ (↑m : ℝ) - (↑R.scale : ℝ) →
                    (0 : ℝ) ≤ (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ →
                      (0 : ℝ) ≤ lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale ((2 :
                        ℝ) * q) →
                        (0 : ℝ) ≤ bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ)
                          * q) →
                          bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q) ≤
                              (1 : ℝ) + slotProductBound d (Disorder.cstar M) (CB *
                                (Disorder.cstar M)⁻¹) →
                            (0 : ℝ) ≤ (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale :
                              ℝ)))) →
                              (0 : ℝ) ≤
                                  (M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)) + M.gamma) *
                                    (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)))) →
                                (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                        (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) : ℝ) ^ (2 : ℕ) *
                                      lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale
                                        ((2 : ℝ) * q) ≤
                                    (4 : ℝ) * (4 : ℝ) * lambdaSlotFactorBound d (CL *
                                      (Disorder.cstar M)⁻¹) →
                                  ((↑(Annealed.sigmaBar M m) : ℝ) * (↑(Annealed.sigmaBar M
                                    (R.scale - (2 : ℤ))) : ℝ)⁻¹ -
                                          (1 : ℝ)) ^
                                        (2 : ℕ) ≤
                                      C2b * ((320004 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ))
                                        + M.gamma)) *
                                        (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale :
                                          ℝ)))) →
                                    (0 : ℝ) ≤
                                        ((↑(Annealed.sigmaBar M m) : ℝ) *
                                              (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) : ℝ)⁻¹ -
                                            (1 : ℝ)) ^
                                          (2 : ℕ) →
                                      (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
                                              (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) : ℝ) ^
                                                (2 : ℕ) *
                                            ((↑(Annealed.sigmaBar M m) : ℝ) *
                                                  (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) :
                                                    ℝ)⁻¹ -
                                                (1 : ℝ)) ^
                                              (2 : ℕ) *
                                          (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹)
                                            R.scale ((2 : ℝ) * q) *
                                            bracketMajorant d M (CB * (Disorder.cstar M)⁻¹)
                                              R.scale ((2 : ℝ) * q)) ≤
                                        secondRatioLegBound d (Disorder.cstar M) (CL *
                                          (Disorder.cstar M)⁻¹)
                                            (CB * (Disorder.cstar M)⁻¹) C2b *
                                          (q *
                                            ((M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)) + M.gamma) *
                                              (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) -
                                                (↑R.scale : ℝ)))))) := by
  intro d CL CB C2b hC2b0 M m R q hq hEL0 hEB0 hgam0 ht hsig0 hlam0 hbrB0 hbrBle hwt0 hslot0
    hratio hdelta hdelta0
  have hgroup : ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
      ((Annealed.sigmaBar M m : ℝ) *
        ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 *
      (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
        bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q)) =
      (((Annealed.sigmaBar M m : ℝ))⁻¹ *
          (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
          lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q)) *
        (((Annealed.sigmaBar M m : ℝ) *
            ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 *
          bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q)) := by
    ring
  rw [hgroup]
  have hY : ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 *
      bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) ≤
      C2b * (320004 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma)) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) *
        (1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) := by
    refine mul_le_mul hdelta hbrBle hbrB0 ?_
    refine mul_nonneg (mul_nonneg hC2b0.le ?_) hwt0
    have h1 := mul_nonneg hgam0.le ht
    linarith only [h1, hgam0]
  have hX0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
      lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) :=
    mul_nonneg (mul_nonneg hsig0 (sq_nonneg _)) hlam0
  have hY0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 *
      bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) :=
    mul_nonneg hdelta0 hbrB0
  have hprod := mul_le_mul hratio hY hY0
    (by
      have h2 : (0 : ℝ) < lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹) :=
        lambdaSlotFactorBound_pos d hEL0
      positivity)
  refine le_trans hprod ?_
  have hqlift : (1 : ℝ) ≤ q := hq
  have hbase : (0 : ℝ) ≤ secondRatioLegBound d (Disorder.cstar M)
      (CL * (Disorder.cstar M)⁻¹) (CB * (Disorder.cstar M)⁻¹) C2b *
      ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))) :=
    mul_nonneg (secondRatioLegBound_pos d hEL0 hEB0 hC2b0).le hslot0
  have hlift := mul_le_mul_of_nonneg_left hqlift hbase
  have hidL : 4 * 4 * lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹) *
      (C2b * (320004 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma)) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) *
        (1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹))) =
      secondRatioLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
          (CB * (Disorder.cstar M)⁻¹) C2b *
        ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))) * 1 := by
    rw [secondRatioLegBound]
    ring
  have hidR : secondRatioLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
        (CB * (Disorder.cstar M)⁻¹) C2b *
      ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))) * q =
      secondRatioLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
          (CB * (Disorder.cstar M)⁻¹) C2b *
        (q * ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) := by ring
  linarith only [hlift, hidL, hidR]

private theorem perCubeSlotSecond_comparisonBounds1 :
    ∀ (d : ℕ) (CL CB C2b : ℝ) (_ : (0 : ℝ) < C2b)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ C2b⁻¹ ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ (1 / 8 : ℝ) →
              ∀ (m j : ℤ),
                j - (2 : ℤ) ≤ m →
                  ((↑(Annealed.sigmaBar M m) : ℝ) * (↑(Annealed.sigmaBar M (j - (2 : ℤ))) : ℝ)⁻¹ -
                    (1 : ℝ)) ^ (2 : ℕ) ≤
                    C2b *
                        min (1 : ℝ)
                            (M.gamma * ((↑m : ℝ) - (↑j : ℝ) + (2 : ℝ)) +
                              M.gamma ^ (3 / 5 : ℝ) * |Real.log M.gamma| ^ (2 : ℕ)) ^
                          (2 : ℕ) *
                      (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑j : ℝ)))))
      (M : ABKModel d) (_ : M.gamma ≤ (1 / 8 : ℝ)) (m : ℤ) (R : TriadicCube d) (_ : R.scale ≤ m)
        (q : ℝ)
      (_ : (1 : ℝ) ≤ q) (_ : (0 : ℝ) < Disorder.cstar M) (_ : (0 : ℝ) < CL * (Disorder.cstar M)⁻¹)
      (_ : (0 : ℝ) < CB * (Disorder.cstar M)⁻¹) (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≤ (1 : ℝ))
      (_ : M.gamma ≤ (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ (2 : ℝ) * q) (_ : (0 : ℝ) ≤ (8 : ℝ) * q)
      (_ : (2 : ℝ) * q ≤ M.gamma⁻¹) (_ : (0 : ℝ) ≤ (↑m : ℝ) - (↑R.scale : ℝ))
      (_ : M.gamma ≤ C2b⁻¹ ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ))
      (_ :
        ∀ (j : ℤ),
          (3 : ℝ) ^ (M.gamma * (↑j : ℝ)) * (↑(Annealed.sigmaBar M (j - (1 : ℤ))) : ℝ)⁻¹ ≤
            (16 : ℝ) * ((√(Disorder.cstar M))⁻¹ * √M.gamma))
      (_ :
        ∀ (m : ℤ),
          (3 : ℝ) ^ (M.gamma * (↑m : ℝ)) * (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ ≤
            (4 : ℝ) * ((√(Disorder.cstar M))⁻¹ * √M.gamma))
      (_ :
        ∀ (m j : ℤ),
          j - (2 : ℤ) ≤ m → (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ * (↑(Annealed.sigmaBar M (j - (2 :
            ℤ))) : ℝ) ≤ (4 : ℝ))
      (_ :
        ∀ (j : ℤ), (↑(Annealed.sigmaBar M (j - (2 : ℤ))) : ℝ) * (↑(Annealed.sigmaBar M (j - (1 :
          ℤ))) : ℝ)⁻¹ ≤ (4 : ℝ))
      (_ : √M.gamma * √M.gamma = M.gamma) (_ : (0 : ℝ) ≤ (↑(Annealed.sigmaBar M m) : ℝ)⁻¹)
      (_ : (0 : ℝ) < (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) : ℝ))
      (_ : (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (R.scale - (1 : ℤ))) : ℝ)⁻¹)
      (_ : (0 : ℝ) ≤ lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q))
      (_ : (0 : ℝ) ≤ bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((4 : ℝ) * q))
      (_ : (0 : ℝ) ≤ bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q))
      (_ : (0 : ℝ) ≤ lambdaSlotFactor d M (CL * (Disorder.cstar M)⁻¹) ((2 : ℝ) * q))
      (_ :
        lambdaSlotFactor d M (CL * (Disorder.cstar M)⁻¹) ((2 : ℝ) * q) ≤
          lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹))
      (_ :
        bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((4 : ℝ) * q) ≤
          (1 : ℝ) + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹))
      (_ :
        bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q) ≤
          (1 : ℝ) + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹))
      (_ : (0 : ℝ) ≤ slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹))
      (_ : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ))))),
      (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ *
            (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q) *
              (bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((4 : ℝ) * q) *
                valueSlotMajorant M m R.scale ((8 : ℝ) * q) ^ (2 : ℕ))) ≤
          secondValueLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹) (CB *
            (Disorder.cstar M)⁻¹) *
            (q *
              ((M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)) + M.gamma) *
                (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)))))) ∧
        (↑(Annealed.sigmaBar M m) : ℝ)⁻¹ * (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) : ℝ) ^ (2 :
          ℕ) *
              ((↑(Annealed.sigmaBar M m) : ℝ) * (↑(Annealed.sigmaBar M (R.scale - (2 : ℤ))) : ℝ)⁻¹
                - (1 : ℝ)) ^ (2 : ℕ) *
            (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q) *
              bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale ((2 : ℝ) * q)) ≤
          secondRatioLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹) (CB *
            (Disorder.cstar M)⁻¹) C2b *
            (q *
              ((M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)) + M.gamma) *
                (3 : ℝ) ^ ((2 : ℝ) * (M.gamma * ((↑m : ℝ) - (↑R.scale : ℝ)))))) := by
  intro d CL CB C2b hC2b0 hB2 M hgam m R _ q hq _ hEL0 hEB0 hgam0 hgam1 hgam2 h2q0 h8q0 h2qg ht
    hregB2 hgB5 hgM hgB1 hgIdx hsg hsig0 hsigA0 hsigB0 hlam0 hbrA0 hbrB0 hfac0 hfacle hbrAle
      hbrBle hSPB0 hwt0
  have hslot0 : (0 : ℝ) ≤ (M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
      (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) := by
    refine mul_nonneg ?_ hwt0
    have := mul_nonneg hgam0.le ht
    linarith only [this, hgam0]
  -- (a) the value leg
  have hvalue : ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
        (bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (4 * q) *
          valueSlotMajorant M m R.scale (8 * q) ^ 2)) ≤
      secondValueLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
          (CB * (Disorder.cstar M)⁻¹) *
        (q * ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) := by
    have hstep := mulLeMul4 hsig0 hlam0 hbrA0 (sq_nonneg _)
      (inv_sigmaBar_le_weight M m (hgM m))
      (lambdaSlotMajorant_le_weight d M hEL0 R.scale h2q0 h2qg (hgB5 R.scale))
      hbrAle
      (valueSlotMajorant_sq_le M m R.scale h8q0 hgam2 ht)
    refine le_trans hstep ?_
    have hgt := rpow_three_gauge_triple (M.gamma * (m : ℝ)) (M.gamma * (R.scale : ℝ))
    have hgt2 : (3 : ℝ) ^ (M.gamma * (m : ℝ) - M.gamma * (R.scale : ℝ)) =
        (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (R.scale : ℝ))) := by
      congr 1
      ring
    have hregroup : (3 : ℝ) ^ (-(M.gamma * (m : ℝ))) *
        (4 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma)) *
        ((3 : ℝ) ^ (-(M.gamma * (R.scale : ℝ))) *
            (16 * ((Real.sqrt (Disorder.cstar M))⁻¹ * Real.sqrt M.gamma) *
              lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹)) *
          ((1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) *
            (2 * (gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2) *
              (8 * q * (1 + ((m : ℝ) - (R.scale : ℝ)))) *
              (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ)))))) =
        512 * ((Real.sqrt (Disorder.cstar M))⁻¹ * (Real.sqrt (Disorder.cstar M))⁻¹) *
          lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹) *
          (1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) *
          (2 * (gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2)) * q *
          (1 + ((m : ℝ) - (R.scale : ℝ))) *
          (Real.sqrt M.gamma * Real.sqrt M.gamma) *
          ((3 : ℝ) ^ (-(M.gamma * (m : ℝ))) *
            ((3 : ℝ) ^ (-(M.gamma * (R.scale : ℝ))) *
              (3 : ℝ) ^ (2 * (M.gamma * (m : ℝ))))) := by ring
    rw [hregroup, hsg, hgt, hgt2]
    have hmono : (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (R.scale : ℝ))) ≤
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) := by
      refine rpow_three_le_rpow_three ?_
      have := mul_nonneg hgam0.le ht
      linarith only [this]
    have hcoef : (0 : ℝ) ≤ 512 *
        ((Real.sqrt (Disorder.cstar M))⁻¹ * (Real.sqrt (Disorder.cstar M))⁻¹) *
        lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹) *
        (1 + slotProductBound d (Disorder.cstar M) (CB * (Disorder.cstar M)⁻¹)) *
        (2 * (gammaMomentConst 2 ^ 2 * valueSlotWidth d ^ 2)) * q *
        (1 + ((m : ℝ) - (R.scale : ℝ))) * M.gamma := by
      have h1 : (0 : ℝ) ≤ (Real.sqrt (Disorder.cstar M))⁻¹ :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      have h2 : (0 : ℝ) < lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹) :=
        lambdaSlotFactorBound_pos d hEL0
      have h3 : (0 : ℝ) < 1 + slotProductBound d (Disorder.cstar M)
          (CB * (Disorder.cstar M)⁻¹) := by linarith only [hSPB0]
      have h4 : (0 : ℝ) ≤ 1 + ((m : ℝ) - (R.scale : ℝ)) := by linarith only [ht]
      positivity
    have hstep2 := mul_le_mul_of_nonneg_left hmono hcoef
    refine le_trans hstep2 (le_of_eq ?_)
    rw [secondValueLegBound]
    ring
  -- (b) the (B2) leg
  have hratio : ((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
      lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) ≤
      4 * 4 * lambdaSlotFactorBound d (CL * (Disorder.cstar M)⁻¹) := by
    rw [lambdaSlotMajorant_eq_mul]
    have hid : ((Annealed.sigmaBar M m : ℝ))⁻¹ *
        (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
        (((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ *
          lambdaSlotFactor d M (CL * (Disorder.cstar M)⁻¹) (2 * q)) =
        ((Annealed.sigmaBar M m : ℝ))⁻¹ * (Annealed.sigmaBar M (R.scale - 2) : ℝ) *
          ((Annealed.sigmaBar M (R.scale - 2) : ℝ) *
            ((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹) *
          lambdaSlotFactor d M (CL * (Disorder.cstar M)⁻¹) (2 * q) := by ring
    rw [hid]
    refine mul_le_mul ?_ hfacle hfac0 (by norm_num)
    exact mul_le_mul (hgB1 m R.scale (by omega)) (hgIdx R.scale)
      (mul_nonneg hsigA0.le hsigB0) (by norm_num)
  have hdelta : ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 ≤
      C2b * (320004 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma)) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) := by
    refine le_trans (hB2 M hregB2 hgam m R.scale (by omega)) ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC2b0.le) hwt0
    exact sigmaBarContinuity_min_sq_le hgam0 hgam1 ht
  have hdelta0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 := sq_nonneg _
  have hratioLeg := @stepThreeSecondTerm_diffusivityRatioBound (d) (CL) (CB) (C2b) (hC2b0) (M) (m)
    (R) (q) (hq) (hEL0) (hEB0) (hgam0) (ht) (hsig0) (hlam0) (hbrB0) (hbrBle) (hwt0) (hslot0)
      (hratio) (hdelta) (hdelta0)
  exact ⟨hvalue, hratioLeg⟩

/-- **The second summand, evaluated.**

`∫⁻ (step3SecondTerm)^q ≤ (ofReal (C_d A q (γ(m−j)+γ) 3^{2γ(m−j)}))^q`: the
anchor's own linear and flat per-scale slots. -/
theorem exists_lintegral_rpow_step3SecondTerm_slot (d : ℕ) [NeZero d] (cstar : ℝ)
    (hcstar : 0 < cstar) :
    ∃ Creg A : ℝ, 0 < Creg ∧ 0 < A ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar →
        M.gamma ≤ (Creg⁻¹) ^ (10 : ℕ) → M.gamma ≤ 1 / 8 → ∀ Cd : ℝ, 0 ≤ Cd →
          ∀ (m : ℤ) (R : TriadicCube d), R.scale ≤ m → ∀ q : ℝ, 1 ≤ q →
            8 * q ≤ M.gamma⁻¹ →
              (∫⁻ omega : Cutoff.CutoffSample d,
                  ENNReal.ofReal (step3SecondTerm Cd M m R omega
                    (lFreeGradSlot m (tailSeriesGauge m) R omega)
                    (lFreeValueSlot m (tailSeriesGauge m) R omega)) ^ q
                  ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
                ENNReal.ofReal (Cd * A * (q *
                  ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
                    (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))))) ^ q := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨CL, CB, hCL6, hCB6, hmom⟩ := exists_lintegral_rpow_step3SecondTerm_le d
  obtain ⟨Cg, hCg0, hgaugeAll⟩ := exists_sigmaBar_gaugePackage d
  obtain ⟨C2b, hC2b0, hB2⟩ := exists_sigmaBar_ratio_sub_one_sq_le_unconditional d
  have hCL0 : (0 : ℝ) < CL := by linarith only [hCL6]
  have hCB0 : (0 : ℝ) < CB := by linarith only [hCB6]
  have hcinv : (0 : ℝ) < cstar⁻¹ := inv_pos.mpr hcstar
  have hEL0 : (0 : ℝ) < CL * cstar⁻¹ := mul_pos hCL0 hcinv
  have hEB0 : (0 : ℝ) < CB * cstar⁻¹ := mul_pos hCB0 hcinv
  have hCbig0 : (0 : ℝ) < max (max (max CL CB) Cg) C2b :=
    lt_of_lt_of_le hCL0 (le_trans (le_trans (le_max_left CL CB) (le_max_left _ _))
      (le_max_left _ _))
  refine ⟨max (max (max CL CB) Cg) C2b * cstar⁻¹,
    secondValueLegBound d cstar (CL * cstar⁻¹) (CB * cstar⁻¹) +
      secondRatioLegBound d cstar (CL * cstar⁻¹) (CB * cstar⁻¹) C2b,
    mul_pos hCbig0 hcinv, ?_, ?_⟩
  · exact add_pos (secondValueLegBound_pos d hd hcstar hEL0 hEB0)
      (secondRatioLegBound_pos d hEL0 hEB0 hC2b0)
  intro M hcs hreg hgam Cd hCd m R hkm q hq h8q
  subst hcs
  have hcs0 : (0 : ℝ) < Disorder.cstar M := hcstar
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgam1 : M.gamma ≤ 1 := by linarith only [hgam]
  have hgam2 : M.gamma ≤ 1 / 2 := by linarith only [hgam]
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h2q0 : (0 : ℝ) ≤ 2 * q := by linarith only [hq0]
  have h4q0 : (0 : ℝ) ≤ 4 * q := by linarith only [hq0]
  have h8q0 : (0 : ℝ) ≤ 8 * q := by linarith only [hq0]
  have h2qg : 2 * q ≤ M.gamma⁻¹ := by linarith only [h8q, hq0]
  have h8qg : 2 * (4 * q) ≤ M.gamma⁻¹ := by linarith only [h8q]
  have h4qg : 2 * (2 * q) ≤ M.gamma⁻¹ := by linarith only [h8q, hq0]
  have ht : (0 : ℝ) ≤ (m : ℝ) - (R.scale : ℝ) := by
    have hcast : (R.scale : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    linarith only [hcast]
  -- the three regimes
  have hbound : ∀ C : ℝ, 0 < C → C ≤ max (max (max CL CB) Cg) C2b →
      M.gamma ≤ (C⁻¹) ^ (10 : ℕ) * (Disorder.cstar M) ^ (10 : ℕ) := by
    intro C hC hCle
    refine gamma_regime_of_cstar_scaled (le_trans hreg ?_)
    refine pow_le_pow_left₀ (inv_nonneg.mpr (mul_pos hCbig0 (inv_pos.mpr hcs0)).le) ?_ 10
    exact inv_anti₀ (mul_pos hC (inv_pos.mpr hcs0))
      (mul_le_mul_of_nonneg_right hCle (inv_pos.mpr hcs0).le)
  have hregMom : M.gamma ≤ ((max CL CB)⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 :=
    hbound (max CL CB) (lt_of_lt_of_le hCL0 (le_max_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  have hregG : M.gamma ≤ (Cg⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 :=
    hbound Cg hCg0 (le_trans (le_max_right _ _) (le_max_left _ _))
  have hregB2 : M.gamma ≤ (C2b⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 :=
    hbound C2b hC2b0 (le_max_right _ _)
  obtain ⟨hgB5, hgM, hgB1, hgIdx⟩ := hgaugeAll M hregG
  refine le_trans (hmom M hregMom hgam Cd hCd m R hkm q hq) ?_
  refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hq0.le
  -- the real evaluation
  have hsg : Real.sqrt M.gamma * Real.sqrt M.gamma = M.gamma :=
    Real.mul_self_sqrt hgam0.le
  have hsig0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M m : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M m).2.le
  have hsigA0 : (0 : ℝ) < (Annealed.sigmaBar M (R.scale - 2) : ℝ) :=
    (Annealed.sigmaBar M (R.scale - 2)).2
  have hsigB0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (R.scale - 1) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Annealed.sigmaBar M (R.scale - 1)).2.le
  have hlam0 : (0 : ℝ) ≤
      lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) :=
    lambdaSlotMajorant_nonneg d M _ R.scale h2q0
  have hbrA0 : (0 : ℝ) ≤
      bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (4 * q) :=
    bracketMajorant_nonneg d M _ R.scale h4q0
  have hbrB0 : (0 : ℝ) ≤
      bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q) :=
    bracketMajorant_nonneg d M _ R.scale h2q0
  have hfac0 : (0 : ℝ) ≤ lambdaSlotFactor d M (CL * (Disorder.cstar M)⁻¹) (2 * q) := by
    have h1 : (0 : ℝ) ≤ lambdaUpscaleConst d * Support.cgEllipLowerConstant d :=
      mul_nonneg (lambdaUpscaleConst_pos d).le (Support.cgEllipLowerConstant_pos d).le
    have h2 : (0 : ℝ) ≤ gammaMomentConst (1 / 3) * (2 * q) ^ ((1 / 3 : ℝ))⁻¹ *
        (lambdaUpscaleConst d * lambdaMaxOrliczConst d *
          Proportion.cgTailScale M (CL * (Disorder.cstar M)⁻¹)) := by
      refine mul_nonneg (mul_nonneg (gammaMomentConst_pos (by norm_num)).le
        (Real.rpow_nonneg h2q0 _)) ?_
      exact mul_nonneg (mul_nonneg (lambdaUpscaleConst_pos d).le
        (lambdaMaxOrliczConst_pos d).le) (Proportion.cgTailScale_pos M _).le
    rw [lambdaSlotFactor]
    linarith only [h1, h2]
  have hfacle := lambdaSlotFactor_le d M hEL0 h2q0 h2qg
  have hbrAle := bracketMajorant_le d M hEB0 R.scale (r := 4 * q) h4q0 h8qg hgam2
    (hgB5 R.scale)
  have hbrBle := bracketMajorant_le d M hEB0 R.scale (r := 2 * q) h2q0 h4qg hgam2
    (hgB5 R.scale)
  have hSPB0 : (0 : ℝ) ≤ slotProductBound d (Disorder.cstar M)
      (CB * (Disorder.cstar M)⁻¹) := slotProductBound_nonneg d hEB0
  have hwt0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  obtain ⟨hvalue, hratioLeg⟩ :=
    @perCubeSlotSecond_comparisonBounds1 (d) (CL) (CB) (C2b) (hC2b0) (hB2) (M) (hgam) (m) (R)
      (hkm) (q) (hq) (hcstar) (hEL0) (hEB0) (hgam0) (hgam1) (hgam2) (h2q0) (h8q0) (h2qg) (ht)
        (hregB2) (hgB5) (hgM) (hgB1) (hgIdx) (hsg) (hsig0) (hsigA0) (hsigB0) (hlam0) (hbrA0)
          (hbrB0) (hfac0) (hfacle) (hbrAle) (hbrBle) (hSPB0) (hwt0)
  -- (c) the two legs, summed
  rw [secondTermMajorant]
  have hA := mul_le_mul_of_nonneg_left hvalue hCd
  have hB := mul_le_mul_of_nonneg_left hratioLeg hCd
  have hidA : Cd * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
        (bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (4 * q) *
          valueSlotMajorant M m R.scale (8 * q) ^ 2))) =
      Cd * ((Annealed.sigmaBar M m : ℝ))⁻¹ *
        (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
          (bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (4 * q) *
            valueSlotMajorant M m R.scale (8 * q) ^ 2)) := by ring
  have hidB : Cd * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
      (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
      ((Annealed.sigmaBar M m : ℝ) *
        ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2 *
      (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
        bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q))) =
      Cd * (((Annealed.sigmaBar M m : ℝ))⁻¹ *
        (Annealed.sigmaBar M (R.scale - 2) : ℝ) ^ 2 *
        ((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (R.scale - 2) : ℝ))⁻¹ - 1) ^ 2) *
        (lambdaSlotMajorant d M (CL * (Disorder.cstar M)⁻¹) R.scale (2 * q) *
          bracketMajorant d M (CB * (Disorder.cstar M)⁻¹) R.scale (2 * q)) := by ring
  have hsum : Cd * (secondValueLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
        (CB * (Disorder.cstar M)⁻¹) *
      (q * ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))))) +
      Cd * (secondRatioLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
        (CB * (Disorder.cstar M)⁻¹) C2b *
      (q * ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
        (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ))))))) =
      Cd * (secondValueLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
          (CB * (Disorder.cstar M)⁻¹) +
        secondRatioLegBound d (Disorder.cstar M) (CL * (Disorder.cstar M)⁻¹)
          (CB * (Disorder.cstar M)⁻¹) C2b) *
        (q * ((M.gamma * ((m : ℝ) - (R.scale : ℝ)) + M.gamma) *
          (3 : ℝ) ^ (2 * (M.gamma * ((m : ℝ) - (R.scale : ℝ)))))) := by ring
  linarith only [hA, hB, hidA, hidB, hsum]

end

end Algsuperdiff.Section4.Provider.BoundsEaL
