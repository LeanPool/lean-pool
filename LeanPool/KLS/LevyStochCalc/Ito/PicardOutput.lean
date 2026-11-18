/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputMoments
public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputModification
public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputWeighting
public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputStepDiff

/-!
# The Picard step's output fields

`picardStepOnS2` takes the four fields of its own output — joint measurability, progressive
measurability, almost-sure càdlàg paths and a finite Bielecki norm — as hypotheses. This file
gathers what supplies them: the `L²` bounds on each component of the step, a càdlàg modification
of the step, the resulting self-map of the process space, and the Bielecki-weighted contraction
estimate for the difference of two steps.

## Parts

* `LevyStochCalc.Ito.PicardOutputMoments` — second moments of the drift, diffusion and jump
  components, and finiteness of the Bielecki norm of the step.
* `LevyStochCalc.Ito.PicardOutputModification` — càdlàg adapted modifications of the step and
  the Picard self-map on the space of bounded processes.
* `LevyStochCalc.Ito.PicardOutputWeighting` — the Bielecki weighting inequalities and the
  per-component bounds on the difference of two steps.
* `LevyStochCalc.Ito.PicardOutputStepDiff` — the per-time and Bielecki-norm contraction
  estimates for the difference of two steps.
-/
