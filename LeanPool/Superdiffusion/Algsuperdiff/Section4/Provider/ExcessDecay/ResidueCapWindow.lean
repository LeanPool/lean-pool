/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryGradH
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryWindowNormalized

/-!
# Boundary covering-cube transports

Compatibility import for the six containment-based transports. Their implementations
live in `BoundaryPoincareWindow`, `BoundaryTransports`, and `BoundaryGradH`, where
the geometry-based interfaces derive containment and apply the same results.
The original public declaration names and both public imports are preserved.

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
-/
