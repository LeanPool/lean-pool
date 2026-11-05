/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Results.TheoremOne
public import LeanPool.NairTenenbaum.Smooth.SmoothValuePowerBounds

/-! # The tilted short sum in the large smoothness range -/

@[expose] public section

namespace NairTenenbaum

theorem exists_smoothTilt_cutoff (g : ℕ) {ε δ κ₁ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (_hκ₁ : 0 < κ₁) :
    ∃ w : ℝ, 2 ≤ w ∧ ∀ z : ℝ, w ≤ z →
      κ₁ / Real.log z ≤ ε * δ / 12 ∧ (4 : ℝ) ^ ((g : ℝ) * κ₁) ≤ z := by
  let w := max 2 (max (Real.exp (12 * κ₁ / (ε * δ))) ((4 : ℝ) ^ ((g : ℝ) * κ₁)))
  refine ⟨w, le_max_left _ _, ?_⟩
  intro z hz
  have hz₂ : 2 ≤ z := (le_max_left _ _).trans hz
  have hexp : Real.exp (12 * κ₁ / (ε * δ)) ≤ z :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have Hlog := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at Hlog
  have H := (div_le_iff₀ (mul_pos hε hδ)).mp Hlog
  refine ⟨(div_le_iff₀ (Real.log_pos (by linarith))).mpr (by nlinarith), ?_⟩
  exact (le_max_right _ _).trans ((le_max_right _ _).trans hz)

theorem PolynomialSystem.selectedTilt_mainTerm_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ κ₁ z : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hσ : 0 < σ) (hκ₁ : 0 ≤ κ₁) (hz : 2 ≤ z)
    (hzκ₁ : (4 : ℝ) ^ ((P.total.natDegree : ℝ) * κ₁) ≤ z)
    (hgσ : (P.total.natDegree : ℝ) * σ ≤ 1 / 8) (j : Fin k)
    (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    mainTerm P (selectedTilt F j (Finset.Icc 0 ⌊z⌋₊) (κ₁ / Real.log z)) x y ≤
      selectedMomentUniformBound A B κ₁ (7 / 8) P.total.natDegree P.badDiscriminant * mainTerm P F
          x y := by
  have H := mul_le_mul_of_nonneg_left
    (P.selectedTilt_weightSum_real_le hF hA hB hσ hκ₁ hz hzκ₁ hgσ j x)
    (mul_nonneg hy (sieveProduct_pos P.noFixedPrime x).le)
  exact H.trans_eq (by unfold mainTerm PolynomialSystem.total; ring)

/-- Theorem 1 applied to the varying tilt, with both constants independent
of the smoothness cutoff. -/
theorem exists_tiltedShortSum_bound {g : ℕ} (hg : 0 < g) {A B ε δ κ₁ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hκ₁ : 0 < κ₁) :
    ∃ c₀ w : ℝ, 0 < c₀ ∧ 2 ≤ w ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 4) F →
      ∀ (j : Fin k) (x y z : ℝ), c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x → w ≤ z →
      shortSum P.Q (selectedTilt F j (Finset.Icc 0 ⌊z⌋₊) (κ₁ / Real.log z)) x y ≤
        C P.badDiscriminant * mainTerm P F x y := by
  have hA' : 1 ≤ A * Real.exp κ₁ := one_le_mul_of_one_le_of_one_le hA (Real.one_le_exp_iff.mpr
      hκ₁.le)
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_shortSum_mainTerm_bound hg hA' hB hε hsmall hδ hδ₁
  obtain ⟨w, hw, Hw⟩ := exists_smoothTilt_cutoff g hε hδ hκ₁
  refine ⟨c₀, w, hc₀, hw, fun D => C D * selectedMomentUniformBound A B κ₁ (7 / 8) g D,
    fun D => mul_pos (hC D) (selectedMomentUniformBound_pos _ _ _ _ _ _), ?_⟩
  intro k r P hdeg F hF j x y z hx hy hyx hz
  have hz₂ : 2 ≤ z := hw.trans hz
  obtain ⟨hβ, hzκ₁⟩ := Hw z hz
  have htilt := (hF.selectedTilt (zero_le_one.trans hA) (zero_le_one.trans hB) hκ₁.le hz₂ j).mono
    (by positivity : 0 ≤ A * Real.exp κ₁) (zero_le_one.trans hB) le_rfl le_rfl
    (by linarith : ε * δ / 4 + κ₁ / Real.log z ≤ ε * δ / 3)
  have Hshort := H k r P hdeg _ htilt x y hx hy hyx
  have hx₀ : 0 ≤ x := (by positivity : 0 ≤ c₀ * (polynomialHeight P.total : ℝ) ^ δ).trans hx.le
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hx₀ _).trans hy
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hσ : 0 < ε * δ / 4 := by positivity
  have hgσ : (P.total.natDegree : ℝ) * (ε * δ / 4) ≤ 1 / 8 := by
    rw [hdeg]
    have Hσ : ε * δ / 4 ≤ ε := by nlinarith
    have Hg : (g : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
    exact ((mul_le_mul_of_nonneg_left Hσ (by positivity)).trans
      (mul_le_mul_of_nonneg_right Hg hε.le)).trans hsmall
  have Hmain := P.selectedTilt_mainTerm_le hF (zero_le_one.trans hA) hB hσ hκ₁.le hz₂
    (by simpa only [hdeg] using hzκ₁) hgσ j x hy₀
  rw [hdeg] at Hmain
  exact (Hshort.trans (mul_le_mul_of_nonneg_left Hmain (hC _).le)).trans_eq (by ring)

end NairTenenbaum
