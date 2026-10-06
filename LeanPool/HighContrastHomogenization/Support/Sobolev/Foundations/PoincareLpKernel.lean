/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareLpKernel.Basic
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareLpKernel.SegmentChangeOfVariables
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareLpKernel.TimeCollapse
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareLpKernel.RieszPowerMean

/-!
# Coarse-graining support: Support.Sobolev.Foundations.PoincareLpKernel

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Riesz-kernel tools for convex-domain Poincare (aggregate re-export)

The contents of this file previously lived as one monolithic module; it has
been split along section boundaries into the four modules imported above.
This shim re-exports everything so downstream consumers keep working.
-/
