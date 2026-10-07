/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Cylinder
public import LeanPool.CIVAxisymmetric.Statements.AngularMean
public import LeanPool.CIVAxisymmetric.Statements.AngularMeanScalar
public import LeanPool.CIVAxisymmetric.Statements.IsAxisymmetricOn
public import LeanPool.CIVAxisymmetric.Statements.RotField
public import LeanPool.CIVAxisymmetric.Statements.RotZ

/-!
# Rotations about the axis and the angular mean

This module collects the definitions `CIV.rotZ`, `CIV.rotField`, `CIV.angularMean`,
`CIV.angularMeanScalar` and `CIV.IsAxisymmetricOn` of `eq:interior:average` and
`sec:aniso:notation`, each stated in its own file among the main-result statement files.
-/

public section
