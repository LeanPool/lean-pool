/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module
public import LeanPool.VenNullClockRoundRates.Geometry
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The pole filter and its exact realization by finitely many exponential reads. -/
@[expose] public section
noncomputable section
namespace VenRate
open MeasureTheory VenMask

/-- Exponential difference filter that retains values near the energy pole. -/
def poleFilter (h t : ℝ) : ℝ := 1 - (Real.exp (h * t) - 1) / (2 * h)

theorem filter_bounds {h t : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    1 - t ≤ poleFilter h t ∧ poleFilter h t ≤ 1 - t / 2 := by
  have ht0 := ht.1
  have h0 := mul_nonneg hh.le ht0
  have h1 : h * t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2 hh.le).trans (by simpa using hh1)
  have hn := Real.abs_exp_sub_one_le (x := h * t) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at hn
  have hlo := (le_abs_self _).trans hn
  have hhi := Real.add_one_le_exp (h * t)
  unfold poleFilter
  constructor
  · apply sub_le_sub_left
    apply (div_le_iff₀ (by positivity : 0 < 2 * h)).2
    linarith
  · apply sub_le_sub_left
    apply (le_div_iff₀ (by positivity : 0 < 2 * h)).2
    linarith

private theorem filter_mem {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (y : UnitSphere) :
    poleFilter h (firstEnergy y) ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := (en_bounds 0 y).1
  obtain ⟨hl, hu⟩ := filter_bounds hh hh1 hf
  exact ⟨by linarith [hf.2], by linarith [hf.1]⟩

/-- Integral carrying the k-fold pole filter on the first energy. -/
def filtered (μ : Measure UnitSphere) (U : UnitSphere → ℝ) (h : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ y, U y * Real.exp (x * firstEnergy y) * (poleFilter h (firstEnergy y)) ^ k ∂μ

theorem weighted_integrable {μ : Measure UnitSphere} {U : UnitSphere → ℝ}
    (hi : Integrable U μ) (x : ℝ) :
    Integrable (fun y ↦ U y * Real.exp (x * firstEnergy y)) μ := by
  apply hi.mul_bdd (c := Real.exp |x|)
    ((Real.continuous_exp.comp (continuous_const.mul first_cont)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y ↦ by
    change ‖Real.exp (x * firstEnergy y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      x * firstEnergy y ≤ |x| * firstEnergy y :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (en_bounds 0 y).1.1
      _ ≤ |x| := by simpa using mul_le_mul_of_nonneg_left (en_bounds 0 y).1.2 (abs_nonneg x)

theorem filtered_integrable {μ : Measure UnitSphere} {U : UnitSphere → ℝ}
    (hi : Integrable U μ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (k : ℕ) (x : ℝ) :
    Integrable (fun y ↦ U y * Real.exp (x * firstEnergy y) * (poleFilter h (firstEnergy y)) ^
      k) μ := by
  apply (weighted_integrable hi x).mul_bdd (c := 1)
  · have hc : Continuous (fun y ↦ (poleFilter h (firstEnergy y)) ^ k) := by
      unfold poleFilter
      exact (continuous_const.sub (((Real.continuous_exp.comp (continuous_const.mul first_cont)).sub
        continuous_const).div_const _)).pow _
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (filter_mem hh hh1 y).1 _)]
      exact pow_le_one₀ (filter_mem hh hh1 y).1 (filter_mem hh hh1 y).2

private theorem recur {μ : Measure UnitSphere} {U : UnitSphere → ℝ} (hi : Integrable U μ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (k : ℕ) (x : ℝ) :
    filtered μ U h (k + 1) x =
    (1 + 1 / (2 * h)) * filtered μ U h k x - (1 / (2 * h)) * filtered μ U h k (x + h) := by
  unfold filtered
  rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((filtered_integrable hi hh hh1 k x).const_mul _)
        ((filtered_integrable hi hh hh1 k (x + h)).const_mul _)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [add_mul x h, Real.exp_add, pow_succ]
  unfold poleFilter
  ring

/-- Error amplification for the exact order-k finite difference. The samples are
the actual integrals at x, x + h, ..., x + kh, with the same density U throughout. -/
theorem filter_error {μ : Measure UnitSphere} {U : UnitSphere → ℝ} (hi : Integrable U μ)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (k : ℕ) (x e : ℝ)
    (H : ∀ j : ℕ, j ≤ k → |filtered μ U h 0 (x + j * h)| ≤ e) :
    |filtered μ U h k x| ≤ (1 + 1 / h) ^ k * e := by
  induction k generalizing x with
  | zero => simpa using H 0 (by omega)
  | succ k ih =>
    have hj (j : ℕ) (hl : j ≤ k) : |filtered μ U h 0 (x + h + j * h)| ≤ e := by
      have he : x + h + j * h = x + (↑(j + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [he]; exact H (j + 1) (by omega)
    have ha := ih x (fun j hj ↦ H j (by omega))
    have hb := ih (x + h) hj
    set A := (1 + 1 / (2 * h))
    set B := (1 / (2 * h))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    rw [recur hi hh hh1 k x]
    calc
      _ ≤ |A * filtered μ U h k x| + |B * filtered μ U h k (x + h)| := abs_sub _ _
      _ ≤ A * ((1 + 1 / h) ^ k * e) + B * ((1 + 1 / h) ^ k * e) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hB]
        exact add_le_add (mul_le_mul_of_nonneg_left ha hA) (mul_le_mul_of_nonneg_left hb hB)
      _ = _ := by dsimp [A, B]; rw [pow_succ]; ring
end VenRate
end
