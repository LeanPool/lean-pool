/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AssemblyBoundaryClauseErrorWeighted
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ProviderBoundary
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StitchDisplayLegsErrorWeighted

/-!
# Error-weighted boundary provider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
The weighted provider and its capped specialization are implemented in `ProviderBoundary`.
-/
