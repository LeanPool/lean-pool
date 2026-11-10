/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Ftau.Ftau
public import LeanPool.HyperellipticCurves.Log.Trace.TracePipeline
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Certificate lifting to the power-series level (blueprint `lem:tau-exists`)

The pipelines over `R := O[[X;Y]]` for a local base `O` take certificate packs as
parameters; this file supplies the **lifting machinery** that produces them from
residue-field data. `R` is local with the same residue field as `O`, via the constant
coefficient (`ChabautyColeman.mvSeriesResidue`,
`ChabautyColeman.isUnit_of_mvSeriesResidue_ne_zero`,
`ChabautyColeman.ker_mvSeriesResidue_le_jacobson`), so all conditions live at the
**center**:

* the Bézout certificates lift with prescribed residues by Nakayama
  (`ChabautyColeman.exists_bezout_lift_map`);
* the reduction certificates lift by the degree squeeze
  (`ChabautyColeman.exists_reduceCert_map`), **provided** the reduction step at the center
  attains the generic cofactor degree bound (the "no degree drop" genericity).

These are the inputs of the fold-pack lift (`LeanPool.HyperellipticCurves.Log.Fold.FtauFold`) and of
the
per-disk pack lift (`LeanPool.HyperellipticCurves.Log.Witness.DiskPoint`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section MvSeriesResidue

open IsLocalRing

variable (σ : Type*) (O : Type*) [CommRing O] [IsLocalRing O]

/-- The residue map of `O[[σ]]` over a local base: the residue of the constant coefficient.
Its kernel is the maximal ideal, so Bézout certificates lift along it by Nakayama
(`ChabautyColeman.exists_bezout_lift_map`). -/
noncomputable def mvSeriesResidue : MvPowerSeries σ O →+* ResidueField O :=
  (residue O).comp MvPowerSeries.constantCoeff

theorem mvSeriesResidue_surjective : Function.Surjective (mvSeriesResidue σ O) :=
  residue_surjective.comp fun x ↦ ⟨MvPowerSeries.C x, MvPowerSeries.constantCoeff_C x⟩

theorem isUnit_of_mvSeriesResidue_ne_zero {x : MvPowerSeries σ O}
    (hx : mvSeriesResidue σ O x ≠ 0) : IsUnit x :=
  MvPowerSeries.isUnit_iff_constantCoeff.mpr ((residue_ne_zero_iff_isUnit _).mp hx)

theorem ker_mvSeriesResidue_le_jacobson :
    RingHom.ker (mvSeriesResidue σ O) ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, mem_maximalIdeal x, mem_nonunits_iff]
  exact fun hunit ↦ zero_ne_one (isUnit_zero_iff.mp (hx ▸ hunit.map (mvSeriesResidue σ O)))

end MvSeriesResidue

end ChabautyColeman

end
