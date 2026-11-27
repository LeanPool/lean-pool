/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module
public import LeanPool.VenNullClockRoundRates.Layer
public import LeanPool.VenNullClockRoundRates.Pole
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A finite quantitative separation theorem for the actual two spherical layers.
Constants are independent of the degree, profiles, budget and angle of the
alternative. The uniform read error is an absolute, not relative, error. -/
@[expose] public section
noncomputable section
open MeasureTheory VenMask
namespace VenRate

theorem finite_layer_separation (μ : Measure UnitSphere) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {d b : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hb : 0 < b) :
    ∃ c K T R J : ℝ, 0 < c ∧ 0 < K ∧ 0 < R ∧ R < T ∧ T < 1 ∧ 0 < J ∧
    ∀ {θ a M ε h : ℝ} {w₀ w₁ : UnitSphere → ℝ} (k : ℕ),
      d ≤ 1 - Real.cos θ ^ 2 → 0 < h → h ≤ 1 → (k : ℝ) * h ≤ a →
      Integrable w₀ μ → Integrable w₁ μ →
      (∀ᵐ y ∂μ, 1 ≤ w₀ y) → (∀ᵐ y ∂μ, 1 ≤ w₁ y) →
      (∫ y, w₀ y ∂μ) ≤ M → (∫ y, w₁ y ∂μ) ≤ M →
      DataClose μ w₀ w₁ θ b a ε →
      c * T ^ k ≤ K * M * R ^ k + J * (1 + 1 / h) ^ k * ε := by
  let e := d / 8
  let δ := e ^ 4
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e < 1 := by dsimp [e]; linarith
  have ee : e ^ 2 < 1 := by nlinarith [mul_pos (sub_pos.mpr he1) (by linarith : 0 < 1 + e)]
  have hδ : 0 < δ := pow_pos he _
  have hdlt : δ < e ^ 2 := by
    dsimp [δ]; nlinarith only [mul_pos (sq_pos_of_pos he) (sub_pos.mpr ee)]
  have hδ1 := hdlt.trans ee
  let lo := Real.exp (b * δ)
  let hi := Real.exp (b * e ^ 2)
  let τ := (hi + lo) / 2
  let g := (hi - lo) / 2
  let B := Real.exp b + τ
  have gap : lo < hi := Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hdlt hb)
  have hh : 0 < hi := Real.exp_pos _
  have hl : 0 < lo := Real.exp_pos _
  have ht : 0 < τ := by dsimp [τ]; positivity
  have hg : 0 < g := by dsimp [g]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hc := cap_pos μ (show 0 < δ / 4 by positivity)
  refine ⟨μ.real {y | firstEnergy y < δ / 4}*g, 2 * B, 1 - δ / 4, 1 - δ / 2, 1 + τ,
    mul_pos hc hg, by positivity, by linarith, by linarith, by linarith, by positivity,?_⟩
  intro θ a M ε h w₀ w₁ k hangle hhpos hh1 hgrid i₀ i₁ w₀floor w₁floor m₀ m₁ H
  let U := density w₀ w₁ θ b τ
  let W := fun y ↦ w₀ y + w₁ y
  have intU : Integrable U μ := int_density i₀ i₁ hb.le
  have intW : Integrable W μ := i₀.add i₁
  have pt (y : UnitSphere) :
      U y = w₁ y * (Real.exp (b * secondEnergy θ y) - τ) +
            w₀ y * (τ - Real.exp (b * firstEnergy y)) := by
    dsimp [U, density, tilt]; ring
  have Hbound : ∀ᵐ y ∂μ, 0 ≤ W y ∧ -(B * W y) ≤ U y ∧ (firstEnergy y ≤ δ → g ≤ U y) := by
    filter_upwards [w₀floor, w₁floor] with y hy₀ hy₁
    have h₀ : 0 ≤ w₀ y := by linarith
    have h₁ : 0 ≤ w₁ y := by linarith
    have hE : Real.exp (b * firstEnergy y) ≤ Real.exp b := by
      apply Real.exp_le_exp.mpr
      simpa using mul_le_mul_of_nonneg_left (en_bounds θ y).1.2 hb.le
    have Min₀ : -B ≤ τ - Real.exp (b * firstEnergy y) := by dsimp [B]; linarith
    have Min₁ : -B ≤ Real.exp (b * secondEnergy θ y) - τ := by
      dsimp [B]; linarith [Real.exp_pos b, Real.exp_pos (b * secondEnergy θ y)]
    rw [pt]; dsimp [W]
    refine ⟨add_nonneg h₀ h₁,?_,?_⟩
    · linarith only [mul_le_mul_of_nonneg_left Min₀ h₀, mul_le_mul_of_nonneg_left Min₁ h₁]
    · intro near
      have loy : Real.exp (b * firstEnergy y) ≤ lo :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left near hb.le)
      have hiy : hi ≤ Real.exp (b * secondEnergy θ y) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (cap_separation hd hd1 hangle y near) hb.le)
      have g₀ : g ≤ τ - Real.exp (b * firstEnergy y) := by dsimp [g, τ]; linarith
      have g₁ : g ≤ Real.exp (b * secondEnergy θ y) - τ := by dsimp [g, τ]; linarith
      linarith only [mul_le_mul_of_nonneg_left g₀ h₀, mul_le_mul_of_nonneg_left g₁ h₁,
        mul_le_mul_of_nonneg_right hy₁ hg.le, mul_nonneg h₀ hg.le]
  have PM := pole_integral intU intW hhpos hh1 hδ hδ1.le hg.le hB.le Hbound k
  have moment := filter_error intU hhpos hh1 k 0 ((1 + τ) * ε) (by
    intro j hj
    apply density_sample i₀ i₁ hb.le ht.le H
    constructor
    · positivity
    · simp only [zero_add]; exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
      hhpos.le).trans hgrid)
  have sumW : (∫ y, W y ∂μ) ≤ 2 * M := by
    dsimp [W]; rw [integral_add i₀ i₁]; linarith
  have err := mul_le_mul_of_nonneg_left sumW
    (mul_nonneg hB.le (pow_nonneg (by linarith : 0 ≤ 1 - δ / 2) k))
  linarith only [PM, le_abs_self (filtered μ U h k 0), moment, err]
end VenRate
end
