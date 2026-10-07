/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Cylinder
public import LeanPool.CIVAxisymmetric.Setting.Derivatives
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds
public import LeanPool.CIVAxisymmetric.Statements.BoundedNearOrigin
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Statements.ForceSpatiallyAnalytic
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass

/-!
# The standing hypotheses of the anisotropic theorems

This module collects the hypothesis predicates `CIV.AnisotropicBounds`,
`CIV.ForceC2Bounded`, `CIV.ForceSpatiallyAnalytic`, `CIV.GlobalEnergyClass` and
`CIV.BoundedNearOrigin` of `eq:aniso:bounds`, `eq:interior:force:c-two`,
`eq:interior:force:analytic`, `eq:interior:energy:class` and `eq:interior:regular`,
each of which is stated once in its own file under `CIV.Statements`.
-/

public section
