/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTestOperators
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEquation
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEquationPairings
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Smooth localization of the weak vorticity equation

Multiplying a compact test by a smooth scalar preserves admissibility. The
time and spatial derivative identities below are the calculus terms needed
when localizing `lem:localized-vorticity-energy`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic

namespace ESS

noncomputable section

end

end ESS
