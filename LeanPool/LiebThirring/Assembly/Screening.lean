/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Antisymmetric
public import LeanPool.LiebThirring.Defs.Density
public import LeanPool.LiebThirring.Defs.KineticEnergy
public import LeanPool.LiebThirring.Defs.Coulomb
public import LeanPool.LiebThirring.Defs.RuminConstant
import LeanPool.LiebThirring.Assembly.RuminIntegral
import LeanPool.LiebThirring.Assembly.Young
import LeanPool.LiebThirring.Assembly.Cutoff
import LeanPool.LiebThirring.Kinetic.DensityBasic

/-!
# Screening paid for by kinetic energy

The nearest-nucleus cutoff, extended Young inequality, and kinetic Lieb–Thirring bound pay for
screening. The positive cutoff radius is `κ / (2Z + 1)`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace LiebThirring.Assembly

/-- Positivity of the real kinetic coefficient for a nonzero spin multiplicity. -/
theorem kinetic_coefficient_pos (q : ℕ) (hq : 1 ≤ q) :
    0 < (ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3) := by
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  exact mul_pos (NNReal.coe_pos.mpr ruminConstant_pos) (Real.rpow_pos_of_pos hq' _)

/-- The real kinetic coefficient embeds as the exact extended coefficient. -/
theorem kinetic_coefficient_eq (q : ℕ) (hq : 1 ≤ q) :
    ENNReal.ofReal ((ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3)) =
      (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) := by
  have hq' : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_rpow_of_pos hq', ENNReal.ofReal_natCast]

private theorem screening_scale_eq (κ a : ℝ) (hκ : 0 < κ) (ha : 0 < a) :
    κ ^ (-(3 : ℝ) / 2) * a ^ ((5 : ℝ) / 2) * Real.sqrt (κ / a) = a ^ 2 / κ := by
  have hk : κ ^ (-(3 : ℝ) / 2) * κ ^ ((1 : ℝ) / 2) = κ⁻¹ := by
    rw [← Real.rpow_add hκ]
    norm_num [Real.rpow_neg_one]
  have ha' : a ^ ((5 : ℝ) / 2) / a ^ ((1 : ℝ) / 2) = a ^ 2 := by
    rw [← Real.rpow_sub ha]
    norm_num
  rw [Real.sqrt_eq_rpow, Real.div_rpow hκ.le ha.le]
  calc
    κ ^ (-(3 : ℝ) / 2) * a ^ ((5 : ℝ) / 2) * (κ ^ ((1 : ℝ) / 2) / a ^ ((1 : ℝ) / 2)) =
        (κ ^ (-(3 : ℝ) / 2) * κ ^ ((1 : ℝ) / 2)) * (a ^ ((5 : ℝ) / 2) / a ^ ((1 : ℝ) / 2)) := by
          ring
    _ = a ^ 2 / κ := by rw [hk, ha']; ring

private theorem screening_cost_eq (κ a : ℝ) (hκ : 0 < κ) (ha : 0 < a) (N M : ℕ) :
    ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2) * κ ^ (-(3 : ℝ) / 2)) *
      (8 * Real.pi * (M : ℝ) * a ^ ((5 : ℝ) / 2) * Real.sqrt (κ / a)) +
      (a / (κ / a)) * (N : ℝ) =
      (a ^ 2 / κ) * ((N : ℝ) + 8 * Real.pi * ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2)) * M) := by
  have hscale := screening_scale_eq κ a hκ ha
  have hratio : a / (κ / a) = a ^ 2 / κ := by field_simp
  rw [hratio]
  calc
    _ = ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2)) * (8 * Real.pi * M) *
        (κ ^ (-(3 : ℝ) / 2) * a ^ ((5 : ℝ) / 2) * Real.sqrt (κ / a)) + (a ^ 2 / κ) * N := by ring
    _ = _ := by rw [hscale]; ring
/-- Screening is paid for by the exact kinetic LT hypothesis and the screening cost. -/
theorem screening_of_lt
    (hLT : ∀ (q : ℕ), 1 ≤ q → ∀ (N : ℕ) (ψ : State N q), antisymmetric ψ → ‖ψ‖ = 1 →
      (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
        (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ)
    (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) (N M : ℕ) (R : Fin M → Position)
    (ψ : State N q) (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1) :
    ENNReal.ofReal (2 * (Z : ℝ) + 1) *
      (∫⁻ x : Position, (nearestNucleusDistance R x)⁻¹ * density ψ x) ≤
      kineticEnergy ψ + ENNReal.ofReal
        ((((2 * (Z : ℝ) + 1) ^ 2) / ((ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3))) *
          ((N : ℝ) + 8 * Real.pi * ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2)) * (M : ℝ))) := by
  let κ : ℝ := (ruminConstant : ℝ) * (q : ℝ) ^ (-(2 : ℝ) / 3)
  let a : ℝ := 2 * (Z : ℝ) + 1
  let r : ℝ := κ / a
  let c : ℝ := (2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2) * κ ^ (-(3 : ℝ) / 2)
  have hκ : 0 < κ := kinetic_coefficient_pos q hq
  have ha : 0 < a := by dsimp [a]; positivity
  have hr : 0 < r := div_pos hκ ha
  have hc : 0 < c := young_screening_coefficient_pos κ hκ
  have hmass : (∫⁻ x : Position, density ψ x) = (N : ℝ≥0∞) := by
    have hn : ‖ψ‖₊ = 1 := by apply NNReal.coe_injective; exact hnorm
    rw [density_mass, hn]
    simp only [ENNReal.coe_one, one_pow, mul_one]
  have htail : ENNReal.ofReal a *
      (∫⁻ x : Position, (nearestNucleusDistance R x)⁻¹ * density ψ x) ≤
      (∫⁻ x : Position, nearestNucleusCutoff a r R x * density ψ x) +
        ENNReal.ofReal (a / r) * (N : ℝ≥0∞) := by
    calc
      _ = ∫⁻ x : Position, ENNReal.ofReal a * ((nearestNucleusDistance R x)⁻¹ * density ψ x) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x : Position, nearestNucleusCutoff a r R x * density ψ x +
          ENNReal.ofReal (a / r) * density ψ x := by
        apply lintegral_mono
        intro x
        simpa only [mul_assoc, add_mul] using
          mul_le_mul_left (nearestNucleusInverse_le_cutoff a r hr R x) (density ψ x)
      _ = _ := by
        rw [lintegral_add_right _ ((measurable_density ψ).const_mul (ENNReal.ofReal (a / r))),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmass]
  have hdensitypower : Measurable (fun x : Position => density ψ x ^ ((5 : ℝ) / 3)) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_density ψ)
  have hyoung : (∫⁻ x : Position, nearestNucleusCutoff a r R x * density ψ x) ≤
      ENNReal.ofReal κ * (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) +
        ENNReal.ofReal c * (∫⁻ x : Position, nearestNucleusCutoff a r R x ^ ((5 : ℝ) / 2)) := by
    calc
      _ ≤ ∫⁻ x : Position, ENNReal.ofReal κ * density ψ x ^ ((5 : ℝ) / 3) +
          ENNReal.ofReal c * nearestNucleusCutoff a r R x ^ ((5 : ℝ) / 2) :=
        lintegral_mono (fun x => young_screening κ hκ (nearestNucleusCutoff a r R x) (density ψ x))
      _ = _ := by
        rw [lintegral_add_left (hdensitypower.const_mul (ENNReal.ofReal κ)),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hkinetic : ENNReal.ofReal κ * (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤
      kineticEnergy ψ := by
    rw [kinetic_coefficient_eq q hq]
    exact hLT q hq N ψ hanti hnorm
  have hcutoff := lintegral_nearestNucleusCutoff_rpow_le a r ha.le hr R
  have hbound : (∫⁻ x : Position, nearestNucleusCutoff a r R x * density ψ x) ≤
      kineticEnergy ψ + ENNReal.ofReal c *
        ENNReal.ofReal (8 * Real.pi * (M : ℝ) * a ^ ((5 : ℝ) / 2) * Real.sqrt r) :=
    hyoung.trans (add_le_add hkinetic (mul_le_mul_right hcutoff (ENNReal.ofReal c)))
  have hrad : 0 ≤ 8 * Real.pi * (M : ℝ) * a ^ ((5 : ℝ) / 2) * Real.sqrt r := by positivity
  have hratio : 0 ≤ a / r := (div_pos ha hr).le
  have hcost : ENNReal.ofReal c *
        ENNReal.ofReal (8 * Real.pi * (M : ℝ) * a ^ ((5 : ℝ) / 2) * Real.sqrt r) +
      ENNReal.ofReal (a / r) * (N : ℝ≥0∞) = ENNReal.ofReal
        ((a ^ 2 / κ) * ((N : ℝ) + 8 * Real.pi * ((2 / 5 : ℝ) * (3 / 5 : ℝ) ^ ((3 : ℝ) / 2)) * (M :
          ℝ))) := by
    rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul hc.le,
      ← ENNReal.ofReal_mul hratio,
      ← ENNReal.ofReal_add (mul_nonneg hc.le hrad) (mul_nonneg hratio (Nat.cast_nonneg N))]
    exact congrArg ENNReal.ofReal (screening_cost_eq κ a hκ ha N M)
  exact htail.trans ((add_le_add_left hbound _).trans_eq (by rw [add_assoc, hcost]))

end LiebThirring.Assembly

end
