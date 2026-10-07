/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTangentialCellWeight
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPhaseExpBound
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPolynomialGaussian
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportHeight

/-!
# Weighted factors on short-time cells

The tangential Gaussian, fourth-order normal factor, and fixed normal
phase are controlled by a Gaussian at the dyadic cell midpoint.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- All fixed short-time weight factors on a high-strip cell are
bounded by a center Gaussian and an arbitrarily weak normal quadratic
exponential (`lem:bu-small-time`). -/
theorem bu_short_weighted_cell_factor_bound
    (scale a b : ℝ) (hscale : 0 < scale) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ), 0 ≤ k → ∀ (m : Fin 3 → ℤ) (ell : Fin 2048)
        (z : ParabolicPoint),
        z ∈ buShortShiftedDyadicCell k m ell →
        z ∈ buShortHighStrip scale →
        let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
        Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
          (1 + z.1 2) ^ 4 *
          Real.exp (2 * a *
            (buShortF (z.1 2) z.2 - buShortB scale)) ≤
        C * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          Real.exp (b * Y 2 ^ 2) := by
  obtain ⟨Cphase, hCphase, hPhase⟩ :=
    bu_short_normal_phase_exp_le_quadratic scale a (b / 4) ha (by positivity)
  let Cpoly := 8 * (1 + 4 / (b / 4) ^ 2)
  let C := Real.exp 1 * Cpoly * Cphase * Real.exp (b / 2)
  have hCpoly : 0 < Cpoly := by dsimp [Cpoly]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro k hk m ell z hz hstrip
  dsimp
  have hs : z.2 ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hstrip.2.1, hstrip.2.2⟩
  have hy : 0 ≤ z.1 2 := by
    have hminus : 0 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      positivity
    exact (hminus.trans_le hstrip.1).le
  have hTan := bu_short_tangential_cell_weight_le k hk m ell z hz hs
  have hPoly := bu_short_fourth_power_le_exp_sq
    (b / 4) (z.1 2) (by positivity)
  have hPhasePoint := hPhase z hy hs
  have hZsq := bu_short_shifted_cell_normal_square_le k hk m ell z hz
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  have hNormalArg : b / 2 * z.1 2 ^ 2 ≤ b * Y 2 ^ 2 + b / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hZsq
      (show 0 ≤ b / 2 by positivity)
    nlinarith only [hmul]
  have hNormalExp : Real.exp (b / 2 * z.1 2 ^ 2) ≤
      Real.exp (b / 2) * Real.exp (b * Y 2 ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hNormalArg]
  have hProduct :
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
          (1 + z.1 2) ^ 4 *
          Real.exp (2 * a *
            (buShortF (z.1 2) z.2 - buShortB scale)) ≤
        (Real.exp 1 * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8)) *
          (Cpoly * Real.exp ((b / 4) * z.1 2 ^ 2)) *
          (Cphase * Real.exp ((b / 4) * z.1 2 ^ 2)) := by
    gcongr
  calc
    _ ≤ (Real.exp 1 * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8)) *
          (Cpoly * Real.exp ((b / 4) * z.1 2 ^ 2)) *
          (Cphase * Real.exp ((b / 4) * z.1 2 ^ 2)) := hProduct
    _ = (Real.exp 1 * Cpoly * Cphase) *
          Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          Real.exp (b / 2 * z.1 2 ^ 2) := by
        have hExpNormal :
            Real.exp ((b / 4) * z.1 2 ^ 2) *
              Real.exp ((b / 4) * z.1 2 ^ 2) =
            Real.exp (b / 2 * z.1 2 ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← hExpNormal]
        ring
    _ ≤ (Real.exp 1 * Cpoly * Cphase) *
          Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          (Real.exp (b / 2) * Real.exp (b * Y 2 ^ 2)) := by
        gcongr
    _ = C * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          Real.exp (b * Y 2 ^ 2) := by dsimp [C]; ring

end ESS
