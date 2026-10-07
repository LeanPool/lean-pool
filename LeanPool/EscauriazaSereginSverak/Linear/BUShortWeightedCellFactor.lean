/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedCellWeight

/-!
# The three short-time density factors on a cell

Each factor multiplying rescaled quadratic energy is bounded by a
common center Gaussian.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The tangential factor and both shifted Carleman factors share a
center Gaussian bound on the high normal strip (`lem:bu-small-time`). -/
theorem bu_short_three_cell_factors_bound
    (scale a b : ℝ) (hscale : 0 < scale) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℤ), 0 ≤ k → ∀ (m : Fin 3 → ℤ) (ell : Fin 2048)
        (z : ParabolicPoint),
        z ∈ buShortShiftedDyadicCell k m ell →
        z ∈ buShortHighStrip scale →
        let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
        let Bound := C * Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
          Real.exp (b * Y 2 ^ 2)
        Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
            (1 + z.1 2) ^ 4 ≤ Bound ∧
          buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4 ≤ Bound ∧
          buShortShiftedWeight scale a z ≤ Bound := by
  obtain ⟨C₁, hC₁, hfactorA⟩ :=
    bu_short_weighted_cell_factor_bound scale a b hscale ha hb
  obtain ⟨C₀, hC₀, hfactor0⟩ :=
    bu_short_weighted_cell_factor_bound scale 0 b hscale (by norm_num) hb
  let C := max C₀ C₁
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro k hk m ell z hz hstrip
  dsimp
  let Y := (Foundation.buSmallTimeDyadicCellCenter k m ell).1
  let G := Real.exp (-(Y 0 ^ 2 + Y 1 ^ 2) / 8) *
    Real.exp (b * Y 2 ^ 2)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hs : z.2 ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hstrip.2.1, hstrip.2.2⟩
  have hy : 0 ≤ z.1 2 := by
    have hminus : 0 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      positivity
    exact (hminus.trans_le hstrip.1).le
  have hpoly : 1 ≤ (1 + z.1 2) ^ 4 := by
    have hone : (1 : ℝ) ≤ 1 + z.1 2 := by linarith only [hy]
    exact (by simpa using (pow_le_pow_left₀
      (by norm_num : (0 : ℝ) ≤ 1) hone 4))
  have h0 := hfactor0 k hk m ell z hz hstrip
  have hA := hfactorA k hk m ell z hz hstrip
  have hBase0 :
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        (1 + z.1 2) ^ 4 ≤ C₀ * G := by
    simpa [G, mul_assoc] using h0
  have hBaseA :
      Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
        (1 + z.1 2) ^ 4 *
        Real.exp (2 * a *
          (buShortF (z.1 2) z.2 - buShortB scale)) ≤ C₁ * G := by
    simpa only [G, mul_assoc] using hA
  have hWnonneg : 0 ≤ buShortShiftedWeight scale a z := by
    dsimp [buShortShiftedWeight, buShortCarlemanWeight]
    positivity
  have hsSq : z.2 ^ 2 ≤ 1 := by nlinarith only [hs.1, hs.2]
  have hWpoly : buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4 ≤
      C₁ * G := by
    rw [buShortShiftedWeight_eq scale a z (by linarith only [hs.1])]
    have hfactor0 : 0 ≤
        Real.exp (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
          (1 + z.1 2) ^ 4 *
          Real.exp (2 * a *
            (buShortF (z.1 2) z.2 - buShortB scale)) := by positivity
    calc
      _ = z.2 ^ 2 * (Real.exp
            (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (4 * z.2)) *
          (1 + z.1 2) ^ 4 *
          Real.exp (2 * a *
            (buShortF (z.1 2) z.2 - buShortB scale))) := by ring
      _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hsSq hfactor0
      _ ≤ C₁ * G := by simpa using hBaseA
  have hW : buShortShiftedWeight scale a z ≤ C₁ * G := by
    have h := mul_le_mul_of_nonneg_left hpoly hWnonneg
    have hlow : buShortShiftedWeight scale a z ≤
        buShortShiftedWeight scale a z * (1 + z.1 2) ^ 4 := by
      nlinarith only [h]
    exact hlow.trans hWpoly
  have hC0 : C₀ * G ≤ C * G :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hG
  have hC1 : C₁ * G ≤ C * G :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hG
  refine ⟨?_, ?_, ?_⟩
  · simpa only [G, mul_assoc] using hBase0.trans hC0
  · simpa only [G, mul_assoc] using hWpoly.trans hC1
  · simpa only [G, mul_assoc] using hW.trans hC1

end ESS
