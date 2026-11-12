/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CurvatureOnePeriodicOdometer
public import LeanPool.ApollonianSuperharmonic.CurvatureOneBandCircleClassification
public import LeanPool.ApollonianSuperharmonic.PeriodicQuadraticRemainder
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureGeneratorCocycles

-- [TABLET NODE: BandPeriodicOdometer]

/-!
# BandPeriodicOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPeriodicOdometer (C : BandCircle) :
    ∃ (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction),
      BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h ∧
      GlobalOdometerExtends g h ∧
      (∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
        Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
          ![(a.re : ℝ), (a.im : ℝ)] ∧
        ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) ∧
      ∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
        (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
            (b.1 * (x + v).re + b.2 * (x + v).im) =
          (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
            (b.1 * x.re + b.2 * x.im) := by
-- BODY
  by_cases hc : C.1.1.1 = 1
  · obtain ⟨z, hz⟩ := CurvatureOneBandCircleClassification C hc
    let T : ProtoTile := ⟨{0}, 0⟩
    let h : PartialOdometer := CurvatureOneOdometer z
    let g : IntegerLatticeFunction := fun x =>
      (1 + z.re) * (x.re * (x.re - 1) / 2) -
        z.re * (x.im * (x.im - 1) / 2) + z.im * x.re * x.im
    have result := CurvatureOnePeriodicOdometer C z hz
    dsimp at result
    obtain ⟨hT, htile, hdomain, hvalue, hext, hrep, hcocycle, hperiod⟩ := result
    exact ⟨T, h, g, hT, htile, hext, hcocycle, hperiod⟩
  · have hpos := C.2
    have hcurv : 1 < C.1.1.1 := by omega
    obtain ⟨q, T, h, g, hq, hqC, hT, htile, hext, hzero, hgen⟩ :=
      PositiveCurvatureGeneratorCocycles C hcurv
    have hcocycle := TilingLatticeCocycleExtension C q hq hqC g hgen
    obtain ⟨b, hperiod⟩ := PeriodicQuadraticRemainder C g hcocycle
    exact ⟨T, h, g, hT, htile, hext, hcocycle, ⟨b, hperiod⟩⟩

end ApollonianSuperharmonic

end
