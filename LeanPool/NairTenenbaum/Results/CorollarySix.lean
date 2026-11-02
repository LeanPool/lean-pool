/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Smooth.SmoothTiltBound

/-! # Corollary 6: a smoothness restriction on one polynomial value

The restricted polynomial is explicitly assumed nonconstant. This is needed
for the saving and for the small-value counts; the general polynomial-system
interface also permits constant unit coordinates.
-/

@[expose] public section

namespace NairTenenbaum

open Finset

theorem exists_smoothShortSum_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {A B ε δ κ : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hε : 0 < ε)
    (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hκ : 0 < κ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 4) F →
      ∀ (j : Fin k), 0 < (P.Q j).natDegree → ∀ (x y z : ℝ),
      c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      (2 : ℝ) ^ (κ / (2 * (g : ℝ) ^ 2 * ε)) ≤ z → z ≤ x →
      smoothShortSum P.Q F j x y z ≤
        C P.badDiscriminant * Real.exp (-κ * Real.log x / Real.log z) * mainTerm P F x y := by
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  let q : ℝ := (g : ℝ) ^ 2 * ε
  have hq : 0 < q := by dsimp [q]; positivity
  let c : ℝ := (g : ℝ) + 1 / δ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let κ₁ : ℝ := 8 * κ / q
  have hκ₁ : 0 < κ₁ := by dsimp [κ₁]; positivity
  obtain ⟨c₁, w, hc₁, hw, C₁, hC₁, Htilt⟩ :=
    exists_tiltedShortSum_bound hg hA hB hε hsmall hδ hδ₁ hκ₁
  obtain ⟨K, hK, Habs⟩ := exists_smoothSaving_absorption g hq
  let s := Icc 0 ⌊w⌋₊
  let E₁ : ℝ := 4 * (g : ℝ) * B
  let E₂ : ℝ := 2 * (g : ℝ) * B * fixedSmoothCountBound s (q / (8 * c))
  have hE₁ : 0 < E₁ := by dsimp [E₁]; positivity
  have hE₂ : 0 < E₂ := by
    dsimp [E₂]
    exact mul_pos (by positivity) (fixedSmoothCountBound_pos s (by positivity))
  let c₀ := max 2 (max c₁ (((g : ℝ) + 1) * 2 ^ g))
  have hc₀ : 2 ≤ c₀ := le_max_left _ _
  have hc₀c : c₁ ≤ c₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hc₀g : ((g : ℝ) + 1) * 2 ^ g ≤ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c₀, by linarith, fun D => (E₁ + E₂) * K + C₁ D,
    fun D => add_pos (mul_pos (add_pos hE₁ hE₂) (by linarith)) (hC₁ D), ?_⟩
  intro k r P hdeg F hF j hj x y z hx hy hyx hz _
  have hH : (1 : ℝ) ≤ (polynomialHeight P.total : ℝ) := one_le_polynomialHeight P.total_ne_zero
  have hHδ : 1 ≤ (polynomialHeight P.total : ℝ) ^ δ := Real.one_le_rpow hH hδ.le
  have hcx : c₀ ≤ x := (le_mul_of_one_le_right (by linarith : 0 ≤ c₀) hHδ).trans hx.le
  have hx₂ : 2 ≤ x := hc₀.trans hcx
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hheight : (polynomialHeight P.total : ℝ) ^ δ ≤ x :=
    (le_mul_of_one_le_left (by positivity) (by linarith : 1 ≤ c₀)).trans hx.le
  have hyq : x ^ (4 * q) ≤ y := by simpa only [q, mul_assoc] using hy
  have hzq : (2 : ℝ) ^ (κ / (2 * q)) ≤ z := by simpa only [q, mul_assoc] using hz
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg hx₀.le _).trans hy
  have hz₁ : 1 < z := smooth_cutoff_one_lt hq hκ hzq
  have hσ : 0 < ε * δ / 4 := by positivity
  have hmargin : c * (ε * δ / 4) ≤ 3 * q / 4 := smooth_value_growth_margin hg hε.le hδ hδ₁
  have hvalue : ∀ n ∈ shortInterval x y, ((P.total.eval (n : ℤ)).natAbs : ℝ) ≤ x ^ c :=
    P.shortInterval_value_bound hdeg hx₁ hy₀ hyx hδ hheight (hc₀g.trans hcx)
  have Herror := Habs k r P hdeg.le F hF.nonneg x y κ z hx₂ hyq hκ hzq
  let V := Real.exp (-κ * Real.log x / Real.log z) * mainTerm P F x y
  have hV : 0 ≤ V := mul_nonneg (Real.exp_pos _).le (mainTerm_nonneg P hF.nonneg x hy₀)
  have Herror' : x ^ (7 * q / 8) * F 1 ≤ K * V := by simpa only [V, mul_assoc] using Herror
  by_cases hwz : w ≤ z
  · have Hsmall := P.smallValues_sum_power_bound hdeg hF (zero_le_one.trans hB) hσ.le
      j hj (shortInterval x y) hx₁ hq.le hmargin hvalue
    have Hsmall' : (∑ n ∈ (shortInterval x y).filter
        (fun n : ℕ => (((P.Q j).eval (n : ℤ)).natAbs : ℝ) ≤ x ^ (q / 8)),
        extendArithmeticMap F (fun i => ((P.Q i).eval (n : ℤ)).natAbs)) ≤ E₁ * K * V := by
      calc
        _ ≤ E₁ * (x ^ (7 * q / 8) * F 1) := by simpa only [E₁, mul_assoc] using Hsmall
        _ ≤ E₁ * (K * V) := mul_le_mul_of_nonneg_left Herror' hE₁.le
        _ = _ := by ring
    have Hshort := Htilt k r P hdeg F hF j x y z
      ((mul_le_mul_of_nonneg_right hc₀c (by positivity)).trans_lt hx) hy hyx hwz
    have Hrankin := smoothShortSum_le_small_add_tilt P.Q hF.nonneg j hκ₁.le hz₁
      (Real.rpow_pos_of_pos hx₀ (q / 8)) x y
    have Hexp : Real.exp (-κ₁ * Real.log (x ^ (q / 8)) / Real.log z) =
        Real.exp (-κ * Real.log x / Real.log z) := by
      rw [Real.log_rpow hx₀]
      congr 1
      dsimp [κ₁]
      field_simp
    rw [Hexp] at Hrankin
    have Hlarge : smoothShortSum P.Q F j x y z ≤ (E₁ * K + C₁ P.badDiscriminant) * V := by
      have H := Hrankin.trans (add_le_add Hsmall'
        (mul_le_mul_of_nonneg_left Hshort (Real.exp_pos _).le))
      exact H.trans_eq (by dsimp [V]; ring)
    have HC : E₁ * K + C₁ P.badDiscriminant ≤ (E₁ + E₂) * K + C₁ P.badDiscriminant := by
      nlinarith only [hE₂, hK]
    exact (Hlarge.trans (mul_le_mul_of_nonneg_right HC hV)).trans_eq (by dsimp [V]; ring)
  · have Hfixed := P.fixedSmooth_sum_power_bound hdeg hF (zero_le_one.trans hB) hσ.le
      j hj (shortInterval x y) s hx₁ hc hq hmargin hvalue
    have Hfixed' : smoothShortSum P.Q F j x y w ≤ E₂ * (x ^ (7 * q / 8) * F 1) := by
      simpa only [smoothShortSum, s, E₂, mul_assoc] using Hfixed
    have Hsmall : smoothShortSum P.Q F j x y z ≤ E₂ * K * V := by
      calc
        _ ≤ smoothShortSum P.Q F j x y w := smoothShortSum_mono P.Q hF.nonneg j x y (le_of_not_ge
            hwz)
        _ ≤ E₂ * (x ^ (7 * q / 8) * F 1) := Hfixed'
        _ ≤ E₂ * (K * V) := mul_le_mul_of_nonneg_left Herror' hE₂.le
        _ = _ := by ring
    have HC : E₂ * K ≤ (E₁ + E₂) * K + C₁ P.badDiscriminant := by
      nlinarith only [hE₁, hK, hC₁ P.badDiscriminant]
    exact (Hsmall.trans (mul_le_mul_of_nonneg_right HC hV)).trans_eq (by dsimp [V]; ring)

/-- Corollary 6 with the nonconstancy of the restricted coordinate explicit.
Any coordinate may be restricted, rather than only the last one. -/
def CorollarySix : Prop :=
  ∀ (k r g : ℕ), 0 < k → 0 < r → 0 < g →
  ∀ (A B ε δ κ : ℝ), 1 ≤ A → 1 ≤ B → 0 < ε → ε < 1 / (8 * (g : ℝ) ^ 2) →
    0 < δ → δ ≤ 1 → 0 < κ →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C : ℕ → ℝ, (∀ D, 0 < C D) ∧
      ∀ (P : PolynomialSystem k r), P.total.natDegree = g →
      ∀ (F : ArithmeticMap k), Admissible A B (ε * δ / 4) F →
      ∀ (j : Fin k), 0 < (P.Q j).natDegree → ∀ (x y z : ℝ),
      c₀ * (polynomialHeight P.total : ℝ) ^ δ < x →
      x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y → y ≤ x →
      (2 : ℝ) ^ (κ / (2 * (g : ℝ) ^ 2 * ε)) ≤ z → z ≤ x →
      smoothShortSum P.Q F j x y z ≤
        C P.badDiscriminant * Real.exp (-κ * Real.log x / Real.log z) * mainTerm P F x y

theorem corollarySix : CorollarySix := by
  intro k r g _ _ hg A B ε δ κ hA hB hε hsmall hδ hδ₁ hκ
  have hg₀ : (0 : ℝ) < g := by exact_mod_cast hg
  have hsmall' : (g : ℝ) ^ 2 * ε ≤ 1 / 8 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * (g : ℝ) ^ 2)).mp hsmall
    nlinarith
  obtain ⟨c₀, hc₀, C, hC, H⟩ := exists_smoothShortSum_mainTerm_bound hg hA hB hε hsmall' hδ hδ₁ hκ
  exact ⟨c₀, hc₀, C, hC, H k r⟩

end NairTenenbaum
