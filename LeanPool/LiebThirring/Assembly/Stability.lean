/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.IntegratedBaxter
public import LeanPool.LiebThirring.Assembly.Screening

/-!
# Conditional stability of matter

The universally quantified Baxter and kinetic Lieb–Thirring inequalities yield a positive
stability constant chosen before particle counts, charges, nuclei, and the state.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Assembly

private theorem cost_le_uniform (s f : ℝ) (hf : 0 ≤ f) (N M : ℕ) :
    f * ((N : ℝ) + s * (M : ℝ)) ≤ (max 1 s * f) * ((N : ℝ) + (M : ℝ)) := by
  have hN : (N : ℝ) ≤ max 1 s * (N : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 s)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hM : s * (M : ℝ) ≤ max 1 s * (M : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right 1 s) (Nat.cast_nonneg M)
  calc
    _ ≤ f * (max 1 s * (N : ℝ) + max 1 s * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hN hM) hf
    _ = _ := by ring

/-- Conditional assembly with the exact stability conclusion. -/
theorem stability_of_matter_of_baxter_of_lt
    (hB : ∀ (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N),
      attraction (fun _ => Z) R x + baxterCorrection Z R ≤
        electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
          nearestNucleusControl Z R x)
    (hLT : ∀ (q : ℕ), 1 ≤ q → ∀ (N : ℕ) (ψ : State N q),
      antisymmetric ψ → ‖ψ‖ = 1 →
        (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
          (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ)
    (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q),
        (∀ k, z k ≤ Z) → antisymmetric ψ → ‖ψ‖ = 1 →
          (∫⁻ x : Configuration N, attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) ≤
            kineticEnergy ψ +
              (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) +
              nuclearRepulsion z R + (C : ℝ≥0∞) * (N + M : ℕ) := by
  let κ : ℝ := (ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3)
  let a : ℝ := 2 * (Z : ℝ) + 1
  let b : ℝ := (2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2)
  let c : ℝ := max 1 (8 * Real.pi * b) * (a ^ 2 / κ)
  have hκ : 0 < κ := kinetic_coefficient_pos q hq
  have ha : 0 < a := add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) Z.coe_nonneg)
    zero_lt_one
  have hf : 0 < a ^ 2 / κ := div_pos (pow_pos ha 2) hκ
  have hc : 0 < c := mul_pos ((zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)) hf
  refine ⟨Real.toNNReal c, Real.toNNReal_pos.mpr hc, ?_⟩
  intro N M z R ψ hz hanti hnorm
  have hscreen := screening_of_lt hLT q hq Z N M R ψ hanti hnorm
  have hcoef : ENNReal.ofReal a = 2 * (Z : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) Z.coe_nonneg) (by norm_num),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one]
  change ENNReal.ofReal a *
      (∫⁻ x : Position, (nearestNucleusDistance R x)⁻¹ * density ψ x) ≤
      kineticEnergy ψ + ENNReal.ofReal ((a ^ 2 / κ) * ((N : ℝ) +
        8 * Real.pi * b * (M : ℝ))) at hscreen
  rw [hcoef] at hscreen
  have hcost : ENNReal.ofReal ((a ^ 2 / κ) * ((N : ℝ) +
        8 * Real.pi * b * (M : ℝ))) ≤
      (Real.toNNReal c : ℝ≥0∞) * (N + M : ℕ) := by
    calc
      _ ≤ ENNReal.ofReal (c * ((N : ℝ) + (M : ℝ))) :=
        ENNReal.ofReal_le_ofReal (cost_le_uniform (8 * Real.pi * b) (a ^ 2 / κ) hf.le N M)
      _ = _ := by
        rw [ENNReal.ofReal_mul hc.le]
        congr 1
        simp only [← Nat.cast_add, ENNReal.ofReal_natCast]
  have hbax := integratedBaxter_of_baxter hB Z z R ψ hz hnorm
  calc
    _ ≤ _ := hbax
    _ ≤ (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) +
        nuclearRepulsion z R + (kineticEnergy ψ +
          (Real.toNNReal c : ℝ≥0∞) * (N + M : ℕ)) :=
      add_le_add le_rfl (hscreen.trans (add_le_add le_rfl hcost))
    _ = _ := by ac_rfl

end LiebThirring.Assembly

end
