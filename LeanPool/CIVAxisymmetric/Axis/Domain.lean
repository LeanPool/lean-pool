/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.AxisClosedDomain
public import LeanPool.CIVAxisymmetric.Statements.AxisDomain
public import LeanPool.CIVAxisymmetric.Statements.AxisParabolicBoundary
public import LeanPool.CIVAxisymmetric.Statements.Dr
public import LeanPool.CIVAxisymmetric.Statements.DtPast
public import LeanPool.CIVAxisymmetric.Statements.Dz

/-!
# The meridional half-disc and its parabolic boundary

This module collects the definitions of `lem:aniso:axis`: the coordinates `((r, z), t)` of the
meridional half-plane and time, the classical partial derivatives `CIV.dr`, `CIV.dz`, the
one-sided time derivative `CIV.dtPast`, and the sets `CIV.axisDomain`, `CIV.axisClosedDomain` and
`CIV.axisParabolicBoundary`, each stated in its own file among the main-result statement files.
-/

public section
