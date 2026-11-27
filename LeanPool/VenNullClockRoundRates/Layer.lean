/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module
public import LeanPool.VenNullClockRoundRates.Filter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Two calibrated layer curves and the signed density they control. -/
@[expose] public section
noncomputable section
open MeasureTheory VenMask
namespace VenRate

/-- Profile weighted by the downstream exponential read. -/
def tilt (w G : UnitSphere → ℝ) (b : ℝ) (y : UnitSphere) :=
  w y * Real.exp (b * G y)

/-- The scalar read on a layer with downstream strength `b`. -/
def layer (μ : Measure UnitSphere) (w G : UnitSphere → ℝ) (b x : ℝ) :=
  ∫ y, tilt w G b y * Real.exp (x * firstEnergy y) ∂μ

/-- An absolute error bound on both layer differences over the full read interval. -/
def DataClose (μ : Measure UnitSphere) (w₀ w₁ : UnitSphere → ℝ) (θ b a ε : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) a,
    |layer μ w₁ (secondEnergy θ) 0 x - layer μ w₀ firstEnergy 0 x| ≤ ε ∧
    |layer μ w₁ (secondEnergy θ) b x - layer μ w₀ firstEnergy b x| ≤ ε

/-- Signed downstream-layer difference after subtracting the scaled zero-layer density. -/
def density (w₀ w₁ : UnitSphere → ℝ) (θ b τ : ℝ) (y : UnitSphere) :=
  (tilt w₁ (secondEnergy θ) b y - tilt w₀ firstEnergy b y) - τ * (w₁ y - w₀ y)

theorem int_tilt {μ : Measure UnitSphere} {w G : UnitSphere → ℝ} {b : ℝ}
    (hw : Integrable w μ) (hb : 0 ≤ b) (hc : Continuous G) (hG : ∀ y, G y ≤ 1) :
    Integrable (tilt w G b) μ := by
  apply hw.mul_bdd (c := Real.exp b) (Real.continuous_exp.comp (continuous_const.mul
    hc)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ by
    change ‖Real.exp (b * G y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_left (hG y) hb)

theorem int_density {μ : Measure UnitSphere} {w₀ w₁ : UnitSphere → ℝ}
    {θ b τ : ℝ} (h₀ : Integrable w₀ μ) (h₁ : Integrable w₁ μ) (hb : 0 ≤ b) :
    Integrable (density w₀ w₁ θ b τ) μ :=
  ((int_tilt h₁ hb (second_cont θ) fun y ↦ (en_bounds θ y).2.2).sub
   (int_tilt h₀ hb first_cont fun y ↦ (en_bounds θ y).1.2)).sub ((h₁.sub h₀).const_mul τ)

theorem density_sample {μ : Measure UnitSphere} {w₀ w₁ : UnitSphere → ℝ}
    {θ a b τ ε h : ℝ} (h₀ : Integrable w₀ μ) (h₁ : Integrable w₁ μ) (hb : 0 ≤ b)
    (ht : 0 ≤ τ) (hc : DataClose μ w₀ w₁ θ b a ε) {x : ℝ} (hx : x ∈ Set.Icc 0 a) :
    |filtered μ (density w₀ w₁ θ b τ) h 0 x| ≤ (1 + τ) * ε := by
  let E := fun y ↦ Real.exp (x * firstEnergy y)
  have t₀ := weighted_integrable (int_tilt h₀ hb first_cont fun y ↦ (en_bounds θ y).1.2) x
  have t₁ := weighted_integrable (int_tilt h₁ hb (second_cont θ) fun y ↦ (en_bounds θ y).2.2) x
  have sz (w G : UnitSphere → ℝ) : layer μ w G 0 x = ∫ y, w y * E y ∂μ := by
    simp [layer, tilt, E]
  have eqn : filtered μ (density w₀ w₁ θ b τ) h 0 x =
      (layer μ w₁ (secondEnergy θ) b x - layer μ w₀ firstEnergy b x) -
      τ * (layer μ w₁ (secondEnergy θ) 0 x - layer μ w₀ firstEnergy 0 x) := by
    rw [sz w₀, sz w₁]
    unfold layer filtered
    rw [← integral_sub t₁ t₀, ← integral_sub (weighted_integrable h₁ x) (weighted_integrable h₀ x),
        ← integral_const_mul]
    erw [← integral_sub (t₁.sub t₀) (((weighted_integrable h₁ x).sub
          (weighted_integrable h₀ x)).const_mul τ)]
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro y
    simp only [density, Pi.sub_apply]; ring
  rw [eqn]
  obtain ⟨hA, hB⟩ := hc x hx
  calc
    _ ≤ _ := abs_sub _ _
    _ ≤ ε + τ * ε := by
      rw [abs_mul, abs_of_nonneg ht]
      exact add_le_add hB (mul_le_mul_of_nonneg_left hA ht)
    _ = _ := by ring
end VenRate
end
