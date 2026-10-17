/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Scaling
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CubeControlCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Model

/-!
# LawTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Marginal-law and stationary transport for local controls

Only one-coordinate marginal scaling is used here.  In particular, no claim
of joint shift invariance for the shell sequence is made or needed.
-/

namespace Algsuperdiff.Section3.Cutoff

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The law of a measurable observable of shell `k` is the law of the same
observable after the exact triadic action on the zero shell. -/
theorem map_shellObservable_eq_zero_triadicScale (M : ABKModel d)
    (k : ℤ) (F : ShellField d → ℝ) (hF : Measurable F) :
    Measure.map (fun omega : ShellSeq d => F (omega k)) M.P.toMeasure =
      Measure.map (fun j => F (ShellField.triadicScale M.gamma k j))
        (ShellField.zeroShellLaw M.P).toMeasure := by
  calc
    Measure.map (fun omega : ShellSeq d => F (omega k)) M.P.toMeasure =
        Measure.map F (ShellField.shellMarginalLaw M.P k).toMeasure := by
      simpa only [ShellField.shellMarginalLaw, Function.comp_apply] using!
        (Measure.map_map hF (ShellField.measurable_shellCoordinate k)).symm
    _ = Measure.map F
        ((ShellField.zeroShellLaw M.P).map
          (ShellField.triadicScale M.gamma k)).toMeasure := by
      rw [M.shellPrefix.marginal_scaling k]
    _ = Measure.map (fun j => F (ShellField.triadicScale M.gamma k j))
        (ShellField.zeroShellLaw M.P).toMeasure := by
      simpa only [Function.comp_apply] using!
        Measure.map_map hF (ShellField.measurable_triadicScale M.gamma k)

/-- Distributional form of the local-control transport.  This uses only the
one-coordinate marginal equality for shell `k`. -/
theorem map_localCubeControl_shell_eq_zero (M : ABKModel d)
    (ell k : ℤ) :
    Measure.map (fun omega : ShellSeq d => localCubeControl ell (omega k))
        M.P.toMeasure =
      Measure.map (fun j => Real.rpow 3 (M.gamma * (k : ℝ)) *
        localCubeControl (ell - k) j) (ShellField.zeroShellLaw M.P).toMeasure := by
  rw [map_shellObservable_eq_zero_triadicScale M k (localCubeControl ell)
    (measurable_localCubeControl ell)]
  apply Measure.map_congr
  filter_upwards with j
  exact localCubeControl_triadicScale M.gamma ell k j

/-- Stationarity of the zero shell transports the distribution of any
measurable one-shell observable through a real translation. -/
theorem map_zeroObservable_translate_eq (M : ABKModel d)
    (z : Vec d) (F : ShellField d → ℝ) (hF : Measurable F) :
    Measure.map (fun j => F (ShellField.translate z j))
        (ShellField.zeroShellLaw M.P).toMeasure =
      Measure.map F (ShellField.zeroShellLaw M.P).toMeasure := by
  calc
    Measure.map (fun j => F (ShellField.translate z j))
        (ShellField.zeroShellLaw M.P).toMeasure =
        Measure.map F (Measure.map (ShellField.translate z)
          (ShellField.zeroShellLaw M.P).toMeasure) := by
      simpa only [Function.comp_apply] using!
        (Measure.map_map hF (ShellField.measurable_translate z)).symm
    _ = Measure.map F (ShellField.zeroShellLaw M.P).toMeasure := by
      rw [M.J1.stationary z]

/-- The exact translated unit-cube control has the same zero-shell law as
the origin unit-cube control. -/
theorem map_translatedUnitCubeControl_zero_eq (M : ABKModel d)
    (z : Vec d) :
    Measure.map (translatedUnitCubeControl z) (ShellField.zeroShellLaw M.P).toMeasure =
      Measure.map ShellField.unitCubeValueNorm (ShellField.zeroShellLaw M.P).toMeasure := by
  simpa only [translatedUnitCubeControl] using!
    map_zeroObservable_translate_eq M z ShellField.unitCubeValueNorm
      ShellField.unitCubeValueNorm_measurable

end

end Algsuperdiff.Section3.Cutoff
