/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivComp
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Convergence

/-!
# Coarse-graining support: Support.Sobolev.W1p.ConvexApproxSmoothing

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Convex-domain smoothing operator (aggregate re-export)

Previously a 3373-line monolithic module; now split along thematic boundaries
into the seven files imported above. This shim re-exports everything so
existing downstream consumers keep working unchanged.
-/
