/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.SelectedGenerationRoundedEllipsoidWeightedNormBridge
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderDecoupledTerminalSurface
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCoefficientWeightedNormGauge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.SelectedGenerationPhysicalLipschitz

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical Lipschitz transport at a selected rounded generation

The finite recurrence is transported through its selected rounded grid and
the scalar skew gauge.  The lower radius here is the recurrence start scale;
comparison with an earlier exposed root scale is a separate finite-prefix
argument.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal
open Certificate

noncomputable section

/-- A selected finite terminal controls the physical weighted gradient norm
on every ellipsoid above its own recurrence start. -/
theorem PrintOrderDecoupledFiniteTerminalSurface.physicalLipschitz_from_printStart
    {d : ℕ} [NeZero d] {g c kappa Cid : ℝ}
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (surface : PrintOrderDecoupledFiniteTerminalSurface
      d g c kappa Cid abar a x) :
    let xPrint := printOrderCommonQuantitativeAffineScale d g
      surface.sourceAmplitude (correctorTargetAmplitude c kappa) kappa
      abar surface.X a
    ∀ R : ℝ, xPrint ≤ R →
      ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
        MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
        IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
          ∀ r : ℝ, r ∈ Icc xPrint R →
            weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r) Du ≤
              ENNReal.ofReal
                  ((
                    (ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^
                        (1 / 2 : ℝ) *
                      ENNReal.ofReal (2 * surface.recurrenceConstant) *
                      (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^
                        (1 / 2 : ℝ) +
                    (ENNReal.ofReal
                      ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
                        (1 / 2 : ℝ)).toReal + 1) *
                weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar R) Du := by
  dsimp only
  intro R hstartR u Du hu hweak r hrange
  let geom := RoundedGenerationAnalyticGeometry.ofApplication
    surface.join.application
  let A : ℝ≥0∞ :=
    (ENNReal.ofReal ((12 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ)
  let B : ℝ≥0∞ :=
    (ENNReal.ofReal ((1200 * (d : ℝ)) ^ d)) ^ (1 / 2 : ℝ)
  let N : ℝ≥0∞ :=
    (ENNReal.ofReal ((4800 * (d : ℝ) * Real.sqrt d) ^ d)) ^
      (1 / 2 : ℝ)
  let H : ℝ := 2 * surface.recurrenceConstant
  let K : ℝ≥0∞ := A * ENNReal.ofReal H * B + N
  let C : ℝ := K.toReal + 1
  have hAtop : A ≠ ⊤ := by
    dsimp only [A]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hBtop : B ≠ ⊤ := by
    dsimp only [B]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hNtop : N ≠ ⊤ := by
    dsimp only [N]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hKtop : K ≠ ⊤ := by
    dsimp only [K]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hAtop ENNReal.ofReal_ne_top)
        hBtop, hNtop⟩
  have hKC : K ≤ ENNReal.ofReal C := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKtop).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by
        dsimp only [C]
        exact le_add_of_nonneg_right zero_le_one)
  obtain ⟨_, _, _, _, _, _, hxPrintOneRaw, _, _⟩ := surface.finalCertificate
  have hxPrintOne : 1 ≤ printOrderCommonQuantitativeAffineScale d g
      surface.sourceAmplitude (correctorTargetAmplitude c kappa) kappa
      abar surface.X a := hxPrintOneRaw
  have hR : 0 < R := zero_lt_one.trans_le (hxPrintOne.trans hstartR)
  have hr : 0 < r := zero_lt_one.trans_le (hxPrintOne.trans hrange.1)
  let n : ℤ := Quenched.triadicCeilingIndex
    (printOrderCommonQuantitativeAffineScale d g surface.sourceAmplitude
      (correctorTargetAmplitude c kappa) kappa abar surface.X a)
  let m : ℤ := roundedEllipsoidTerminalGeneration (d := d) R hR
  let Fpull : Vec d → Vec d := fun y ↦
    matVecMul (geom.grid (symmPart abar))
      (Du (matVecMul (geom.grid (symmPart abar)) y))
  let bRounded : CoeffField d :=
    roundedCenteredCoefficientAtGeneration
      surface.join.application.generation
      surface.join.application.generation_admissible abar
      surface.join.application.hS (fun y ↦ a.1 y)
  obtain ⟨w, hw⟩ := exists_roundedEllipsoidTerminalCubeSolutionAtGeneration
    geom a abar surface.join.application.hS
    surface.join.application.aRounded surface.join.application.aRounded_ae
    hR u Du hu hweak
  have hw' : w.toH1.grad = Fpull := by simpa only [Fpull] using hw
  have hpullr := weightedGradNorm_selectedRoundedCenteredPullback geom abar
    surface.join.application.hS (measurableSet_ellipsoid abar r)
    (fun y ↦ a.1 y) Du
  have hpullR := weightedGradNorm_selectedRoundedCenteredPullback geom abar
    surface.join.application.hS (measurableSet_ellipsoid abar R)
    (fun y ↦ a.1 y) Du
  apply weightedGradNorm_le_of_normalizedSkewGauge_le abar
    surface.join.application.hS (fun y ↦ a.1 y)
      (ellipsoid abar r) (ellipsoid abar R) Du (ENNReal.ofReal C)
  rw [hpullr, hpullR]
  by_cases hsmall : r ≤ R / (400 * (d : ℝ))
  · let j : ℤ := roundedEllipsoidOuterGeneration r hr
    have hnj : n ≤ j := by
      simpa only [n, j] using
        (triadicCeilingIndex_cast_le_roundedEllipsoidOuterGeneration
          hxPrintOne hrange.1)
    have hjm : j ≤ m := by
      simpa only [j, m] using
        (roundedEllipsoidOuterGeneration_le_terminalGeneration hr hR hsmall)
    have hjmem : j ∈ Finset.Icc n m := by
      rw [Finset.mem_Icc]
      exact ⟨hnj, hjm⟩
    have henergy := surface.terminal m (hnj.trans hjm) w j hjmem
    have hcube :=
      weightedGradNorm_roundedCenteredCoefficientAtGeneration_le_of_finiteEnergy
        surface.join.application.generation
        surface.join.application.generation_admissible a abar
        surface.join.application.hS surface.join.application.aRounded
        surface.join.application.aRounded_ae m w j hjm H
        (by
          dsimp only [H]
          exact mul_nonneg (by norm_num)
            (zero_le_one.trans surface.recurrenceConstant_ge)) henergy
    rw [hw'] at hcube
    have houter := weightedGradNorm_selectedRoundedPullbackEllipsoid_le_outerCube
      geom abar surface.join.application.hS hr bRounded Fpull
    have hterminal :=
      weightedGradNorm_terminalCube_le_selectedRoundedPullbackEllipsoid
        geom abar surface.join.application.hS hR bRounded Fpull
    have hsmallConstant : A * ENNReal.ofReal H * B ≤ ENNReal.ofReal C :=
      (le_add_of_nonneg_right (show 0 ≤ N from bot_le)).trans hKC
    calc
      weightedGradNorm bRounded
          (selectedRoundedPullbackEllipsoid geom abar r) Fpull ≤
          A * weightedGradNorm bRounded
            (openCubeSet (originCube d j)) Fpull := by
        simpa only [A, j, bRounded, geom,
          RoundedGenerationAnalyticGeometry.ofApplication] using houter
      _ ≤ A * (ENNReal.ofReal H *
          weightedGradNorm bRounded
            (openCubeSet (originCube d m)) Fpull) := by
        apply mul_le_mul_right _ A
        simpa only [bRounded] using hcube
      _ ≤ A * (ENNReal.ofReal H * (B *
          weightedGradNorm bRounded
            (selectedRoundedPullbackEllipsoid geom abar R) Fpull)) :=
        mul_le_mul_right
          (mul_le_mul_right (by simpa only [B, m] using hterminal)
            (ENNReal.ofReal H)) A
      _ = (A * ENNReal.ofReal H * B) *
          weightedGradNorm bRounded
            (selectedRoundedPullbackEllipsoid geom abar R) Fpull := by
        ac_rfl
      _ ≤ ENNReal.ofReal C *
          weightedGradNorm bRounded
            (selectedRoundedPullbackEllipsoid geom abar R) Fpull :=
        mul_le_mul_left hsmallConstant _
  · have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
    have hden : 0 < 400 * (d : ℝ) := mul_pos (by norm_num) hd
    have hnear : R < 400 * (d : ℝ) * r := by
      have hraw := (div_lt_iff₀ hden).mp (lt_of_not_ge hsmall)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hraw
    have hnearNorm :=
      weightedGradNorm_selectedRoundedPullbackEllipsoid_le_of_near_terminal
        geom abar surface.join.application.hS hr hR hrange.2 hnear
          bRounded Fpull
    have hnearConstant : N ≤ ENNReal.ofReal C :=
      (le_add_of_nonneg_left
        (show 0 ≤ A * ENNReal.ofReal H * B from bot_le)).trans hKC
    exact hnearNorm.trans (mul_le_mul_left (by
      simpa only [N] using hnearConstant) _)

end

end Root
end HighContrast
end HCPolySupport
