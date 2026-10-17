/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeCutoffLimitTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainStreamFull

/-!
# ExitTimeCutoffLimitTailData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The exit-time analytic data of a cell

The per-cell exit-time joint of the full stream field asks each cell for six objects: the
solution of the exit-time datum problem for the full field with its continuous representative,
the solutions of the same problem for the truncated fields at every truncation scale with their
representatives, and the constant-coefficient comparator solution with its representative.

All six are produced here, for every model, every sample, every centre and every cube scale.
Solvability is unconditional for each of the three coefficient fields, and each of the three has
a positive scalar symmetric part with a continuous skew part, which is exactly what the interior
estimate needs to turn a solution into a function continuous on the open cube.  Neither the good
cube event nor a bound on the solution enters.

The consequence is that the per-cell analytic data need not be carried as a hypothesis by the
statements that consume them: what they carried is a theorem about the model.

## Main results

* `hasCubeStreamExitTimeData` — every cell carries the exit-time analytic data of the full
  stream field.

## References

* ABK26, the localized exit-time problem of Section 5.2, the one-step Laplace estimate and the
  displacement tail of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support Algsuperdiff.Section5.Trace
open DivergenceFormProcess.Form
open DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup MeasureTheory Set
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-! ## 1. Every cell carries the exit-time analytic data -/

/-- **The exit-time analytic data of a cell exist.**  The exit-time datum problem is solvable on
`y + □_n` for the full stream field, for the truncated field at every truncation scale and for
the constant comparator; and each of those three coefficient fields has the structure that
produces a representative continuous on the open cube.  No event, no smallness and no bound on a
solution is used, so the datum holds at every centre, every cube scale and every sample. -/
theorem hasCubeStreamExitTimeData (M : ABKModel d) (n : ℤ)
    (omega : Field.FullSample d M.gamma) (i : Fin d) (y : Vec d) :
    HasCubeStreamExitTimeData M n omega i y := by
  obtain ⟨w, hw⟩ :=
    exists_isDirichletSolutionAt_linearAxisDatum_streamCoefficient M omega y n i
  obtain ⟨wRep, hwRep⟩ := exists_isCubeRepresentative_streamCoefficient M n y omega hw
  obtain ⟨u, uRep, hu, huRep⟩ := exists_cutoffSolutionFamily_linearAxisDatum M n y omega.1 i
  obtain ⟨v, hv⟩ :=
    exists_isDirichletSolutionAt_comparator M n y (holderSeminormBoundOn_linearAxisDatum i y n)
  obtain ⟨vRep, hvRep⟩ := exists_isCubeRepresentative_comparator M n y hv
  exact ⟨w, wRep, hw, hwRep, u, uRep, v, vRep, hu, huRep, hv, hvRep⟩

end

end Algsuperdiff.Section5.Provider
