/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.RootScalePhysicalLipschitz
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PrintOrderLipschitzFiniteDelayWrapper

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.DecoupledRootPhysicalLipschitz

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Root-facing physical Lipschitz wrapper

The recurrence constant and the finite homothetic prefix are selected before
the coefficient sample.  Their finite product is absorbed into one real
constant at the root surface.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal
open Certificate

noncomputable section

/-- The decoupled root certificate supplies the exact physical Lipschitz row.
After the rate is fixed, the estimate constant is independent of the matrix,
coefficient sample, exposed scale, and solution. -/
theorem exists_decoupledRootPhysicalLipschitz
    (d : ℕ) [NeZero d] :
    ∀ g : ℝ, g ∈ Ico (0 : ℝ) 1 →
      ∃ (Crec c : ℝ),
        1 ≤ Crec ∧ c = (2 * Crec)⁻¹ ∧ c ∈ Ioo (0 : ℝ) 1 ∧
        ∀ kappa : ℝ, ∃ Clip : ℝ, 0 < Clip ∧
          ∀ (abar : Mat d) (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
            DecoupledRootGoodScale d g c kappa abar a x →
            ∀ R : ℝ, x ≤ R →
              ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
                IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
                  ∀ r : ℝ, r ∈ Icc x R →
                    weightedGradNorm (fun y ↦ a.1 y)
                        (ellipsoid abar r) Du ≤
                      ENNReal.ofReal Clip *
                        weightedGradNorm (fun y ↦ a.1 y)
                          (ellipsoid abar R) Du := by
  intro g hg
  obtain ⟨Crec, c, Cid, hCrec, hc, hcRange, hsurface⟩ :=
    exists_decoupledRootFiniteDelaySurface d g hg
  refine ⟨Crec, c, hCrec, hc, hcRange, ?_⟩
  intro kappa
  let q := printOrderToBaseResponseScaleFactor d g kappa
  let T : ℝ≥0∞ :=
    ENNReal.ofReal
      (((ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (2 * Crec) *
            (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^ (1 / 2 : ℝ) +
          (ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
            (1 / 2 : ℝ)).toReal + 1)
  let P : ℝ≥0∞ := (ENNReal.ofReal (q ^ d)) ^ (1 / 2 : ℝ)
  let K : ℝ≥0∞ := T + P * T + P
  let Clip : ℝ := K.toReal + 1
  have hKtop : K ≠ ⊤ := by
    dsimp only [K, T, P]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top,
          ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
              ENNReal.ofReal_ne_top)
            ENNReal.ofReal_ne_top⟩,
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top⟩
  have hKClip : K ≤ ENNReal.ofReal Clip := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKtop).symm
      _ ≤ ENNReal.ofReal Clip := ENNReal.ofReal_le_ofReal (by
        dsimp only [Clip]
        exact le_add_of_nonneg_right zero_le_one)
  have hClip : 0 < Clip := by
    dsimp only [Clip]
    positivity
  refine ⟨Clip, hClip, ?_⟩
  intro abar a x _hx hgood R hxR u Du hu hweak r hrange
  obtain ⟨surface, _hdelay⟩ := hsurface kappa abar a x hgood
  have hrecurrence : surface.recurrenceConstant = Crec := by
    have hinv : (2 * surface.recurrenceConstant)⁻¹ = (2 * Crec)⁻¹ := by
      rw [← surface.target_eq_inverse, ← hc]
    have hmul : 2 * surface.recurrenceConstant = 2 * Crec :=
      inv_injective hinv
    linarith only [hmul]
  have hrow :=
    (open HCPolySupport.HighContrast.Root.PrintOrderDecoupledFiniteTerminalSurface
      (physicalLipschitz_from_rootScale) in
      physicalLipschitz_from_rootScale)
      surface hg R hxR u Du hu hweak r hrange
  have hrowK : weightedGradNorm (fun y ↦ a.1 y)
        (ellipsoid abar r) Du ≤
      K * weightedGradNorm (fun y ↦ a.1 y)
        (ellipsoid abar R) Du := by
    simpa only [K, T, P, q, hrecurrence] using hrow
  exact hrowK.trans (mul_le_mul_left hKClip _)

end

end Root
end HighContrast
end HCPolySupport
