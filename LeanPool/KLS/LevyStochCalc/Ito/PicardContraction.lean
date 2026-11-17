/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardContractionEstimate
public import LeanPool.KLS.LevyStochCalc.Ito.PicardContractionFixedPoint

/-!
# The Picard self-map is a Bielecki contraction

The contraction estimate for the Picard step transfers to the self-map and to the step taken
against a raw state process, the iterates converge in Bielecki norm, and their limit is a fixed
point of the step. The development is split over the following files.

* `LevyStochCalc.Ito.PicardContractionEstimate` — the contraction estimate for the step, for the
  self-map and against a raw state process, and the geometric convergence of the iterates.
* `LevyStochCalc.Ito.PicardContractionFixedPoint` — the limit of the iterates, its Bielecki
  bounds, and the Picard equation it solves along its own path.
-/
