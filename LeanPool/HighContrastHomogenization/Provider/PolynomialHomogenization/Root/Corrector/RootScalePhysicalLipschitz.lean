/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.HomotheticEllipsoidVolume
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.SelectedGenerationPhysicalLipschitz
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PrintOrderLipschitzScaleComparison

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.RootScalePhysicalLipschitz

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-prefix absorption for physical Lipschitz estimates

The homothetic volume identity absorbs the bounded interval between the root
scale and the printed recurrence start.  Above that start, the selected finite
terminal supplies the estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal
open Certificate

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A bounded ratio of positive ellipsoid radii gives a matrix-uniform
weighted-norm comparison. -/
theorem weightedGradNorm_ellipsoid_le_of_le_mul
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    {r R q : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hq : 1 ≤ q) (hRq : R ≤ q * r)
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b (ellipsoid abar r) F ≤
      (ENNReal.ofReal (q ^ d)) ^ (1 / 2 : ℝ) *
        weightedGradNorm b (ellipsoid abar R) F := by
  have hR : 0 < R := hr.trans_le hrR
  have hrestrict := weightedGradNorm_mono_set_le_volumeRatio
    (ellipsoid_mono_of_nonneg abar hr.le hrR)
    (volume_ellipsoid_pos abar hr).ne'
    (volume_ellipsoid_lt_top hS r).ne
    (volume_ellipsoid_pos abar hR).ne'
    (volume_ellipsoid_lt_top hS R).ne b F
  have hratio := volume_ellipsoid_div_le_of_le_mul abar hS hr hrR hq hRq
  have hfactor := ENNReal.rpow_le_rpow hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact hrestrict.trans (mul_le_mul_left hfactor _)

/-- The selected terminal and the finite homothetic prefix control every
physical radius above the root scale. -/
theorem PrintOrderDecoupledFiniteTerminalSurface.physicalLipschitz_from_rootScale
    {g c kappa Cid : ℝ} {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (surface : PrintOrderDecoupledFiniteTerminalSurface
      d g c kappa Cid abar a x)
    (hg : g ∈ Ico (0 : ℝ) 1) :
    let q := printOrderToBaseResponseScaleFactor d g kappa
    let T : ℝ≥0∞ :=
      ENNReal.ofReal
        (((ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (2 * surface.recurrenceConstant) *
              (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^ (1 / 2 : ℝ) +
            (ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
              (1 / 2 : ℝ)).toReal + 1)
    let P : ℝ≥0∞ := (ENNReal.ofReal (q ^ d)) ^ (1 / 2 : ℝ)
    ∀ R : ℝ, x ≤ R →
      ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
        MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
        IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
          ∀ r : ℝ, r ∈ Icc x R →
            weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r) Du ≤
              (T + P * T + P) *
                weightedGradNorm (fun y ↦ a.1 y)
                  (ellipsoid abar R) Du := by
  dsimp only
  intro R hxR u Du hu hweak r hrange
  let xPrint := printOrderCommonQuantitativeAffineScale d g
    surface.sourceAmplitude (correctorTargetAmplitude c kappa) kappa
    abar surface.X a
  let q := printOrderToBaseResponseScaleFactor d g kappa
  let T : ℝ≥0∞ :=
    ENNReal.ofReal
      (((ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (2 * surface.recurrenceConstant) *
            (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^ (1 / 2 : ℝ) +
          (ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
            (1 / 2 : ℝ)).toReal + 1)
  let P : ℝ≥0∞ := (ENNReal.ofReal (q ^ d)) ^ (1 / 2 : ℝ)
  have hq : 1 ≤ q := one_le_printOrderToBaseResponseScaleFactor d g kappa
  have hxPrint : xPrint ≤ q * x := by
    simpa only [xPrint, q] using
      HCPolySupport.HighContrast.Root.PrintOrderDecoupledFiniteTerminalSurface.printOrderScale_le_factor_mul_rootScale
        surface hg
  obtain ⟨_, _, _, _, _, _, hxPrintOne, _, _⟩ := surface.finalCertificate
  have hx : 0 < x := by
    have hxroot : 1 ≤ x := by
      rw [surface.rootScale_eq]
      obtain ⟨_, _, _, _, _, hkappa, hX, _, _⟩ := surface.sourceCertificate
      exact one_le_commonQuantitativeAffineScale hkappa hX
    exact zero_lt_one.trans_le hxroot
  have hr : 0 < r := hx.trans_le hrange.1
  by_cases hRPrint : xPrint ≤ R
  · have hterminal :=
      HCPolySupport.HighContrast.Root.PrintOrderDecoupledFiniteTerminalSurface.physicalLipschitz_from_printStart
        surface
      R hRPrint u Du hu hweak
    by_cases hrPrint : xPrint ≤ r
    · have h := hterminal r ⟨hrPrint, hrange.2⟩
      have hTK : T ≤ T + P * T + P := by
        calc
          T ≤ T + P * T := le_add_of_nonneg_right (show 0 ≤ P * T from bot_le)
          _ ≤ T + P * T + P := le_add_of_nonneg_right (show 0 ≤ P from bot_le)
      exact h.trans (mul_le_mul_left hTK _)
    · have hrxPrint : r ≤ xPrint := le_of_not_ge hrPrint
      have hPrintQr : xPrint ≤ q * r :=
        hxPrint.trans (mul_le_mul_of_nonneg_left hrange.1 (zero_le_one.trans hq))
      have hpref := weightedGradNorm_ellipsoid_le_of_le_mul abar
        surface.join.application.hS hr hrxPrint hq hPrintQr
        (fun y ↦ a.1 y) Du
      have htop := hterminal xPrint ⟨le_rfl, hRPrint⟩
      calc
        weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r) Du ≤
            P * weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar xPrint) Du := by simpa only [P, q] using hpref
        _ ≤ P * (T * weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du) := by
          simpa only [mul_comm, T] using (mul_le_mul_left htop P)
        _ = (P * T) * weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du := by ac_rfl
        _ ≤ (T + P * T + P) * weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du := by
          have hPT : P * T ≤ T + P * T + P := by
            exact (le_add_of_nonneg_left (show 0 ≤ T from bot_le)).trans
              (le_add_of_nonneg_right (show 0 ≤ P from bot_le))
          exact mul_le_mul_left hPT _
  · have hRPrint' : R ≤ xPrint := le_of_not_ge hRPrint
    have hRq : R ≤ q * r := hRPrint'.trans
      (hxPrint.trans (mul_le_mul_of_nonneg_left hrange.1
        (zero_le_one.trans hq)))
    have hpref := weightedGradNorm_ellipsoid_le_of_le_mul abar
      surface.join.application.hS hr hrange.2 hq hRq
      (fun y ↦ a.1 y) Du
    have hP : P ≤ T + P * T + P := by
      exact le_add_of_nonneg_left (show 0 ≤ T + P * T from bot_le)
    exact hpref.trans (mul_le_mul_left (by simpa only [P, q] using hP) _)

end

end Root
end HighContrast
end HCPolySupport
