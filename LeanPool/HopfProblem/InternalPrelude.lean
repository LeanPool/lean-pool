/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Tactic.Abel -- shake: keep
public import Mathlib.Tactic.Choose -- shake: keep
public import Mathlib.Tactic.Continuity -- shake: keep
public import Mathlib.Tactic.Convert -- shake: keep
public import Mathlib.Tactic.Ext -- shake: keep
public import Mathlib.Tactic.FieldSimp -- shake: keep
public import Mathlib.Tactic.FinCases -- shake: keep
public import Mathlib.Tactic.FunProp -- shake: keep
public import Mathlib.Tactic.GCongr -- shake: keep
public import Mathlib.Tactic.Generalize -- shake: keep
public import Mathlib.Tactic.Group -- shake: keep
public import Mathlib.Tactic.IntervalCases -- shake: keep
public import Mathlib.Tactic.Lift -- shake: keep
public import Mathlib.Tactic.Linarith -- shake: keep
public import Mathlib.Tactic.LinearCombination -- shake: keep
public import Mathlib.Tactic.NormNum -- shake: keep
public import Mathlib.Tactic.NormNum.Parity -- shake: keep
public import Mathlib.Tactic.Positivity -- shake: keep
public import Mathlib.Tactic.Ring -- shake: keep
public import Mathlib.Tactic.SplitIfs -- shake: keep
public import Mathlib.Tactic.Tauto -- shake: keep
public import Mathlib.Tactic.WLOG -- shake: keep

/-!
# Internal imports for the Hopf-problem modules

Retain the support imports marked for downstream use by Mathlib, together with the shared tactics.
The original `Prelude` remains available through the project entry points.
-/
