/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.StationaryProjection

/-!
# StationaryCorrector

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the whole-space stationary corrector as a critical gradient field

ABK26, Lemma `l.corrector.limit`,
introduces `w`, "the unique (up to constants) solution of `-Δw = ∇ · f` in `ℝᵈ`
with `∇w ∈ L²_pot` stationary".  In the Hilbert-space realization
of `Algsuperdiff/Probability/StationaryProjection.lean` this determines `∇w`
exactly: `∇w` lies in `stationaryPotentialSubspace` and `∇w + f` is orthogonal
to it, i.e. `∇w + f ∈ stationarySolenoidalSubspace`; equivalently
`∇w = -stationaryPotentialProjection f`.  This is the same construction and the
same sign convention already used by
`Algsuperdiff/Probability/StationaryValueProjection.lean` for the J4 corrector
`zeroShellPotentialCorrector`, but stated for a general translation-invariant
carrier rather than the shell-model one.

This file records the facts about that object that the corrector-limit proof
uses at the level of the probability Hilbert space, in particular the display
`e.pot.sol.decomposition.corrector.limit`

`E[f · ∇w] = -E[|∇w|²]`.

Everything is obtained by specializing the carrier-free lemmas of
`Algsuperdiff/Section3/Provider/Corrector/VariationalEnergy.lean` to
`V = stationaryPotentialSubspace`; no per-realization (spatial) information is
used or produced here.
-/

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Probability.Stationary

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [AddAction (Vec d) Ω]
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-- Stationary potential fields are orthogonal to stationary solenoidal fields.
This is the Hilbert-space content of `∫ p · j = 0` for `p ∈ L²_pot`,
`j ∈ L²_sol`. -/
theorem inner_eq_zero_of_mem_potential_of_mem_solenoidal
    {p j : VectorL2 d μ}
    (hp : p ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (hj : j ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    inner ℝ p j = 0 :=
  Submodule.inner_right_of_mem_orthogonal hp hj


end

end Algsuperdiff.Section3.Provider.Corrector
