/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module -- shake: keep-all

public import Aesop
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.ApplyCongr
public import Mathlib.Tactic.CongrExclamation
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-!
# Tactics for the Nash embedding development

Keep the tactic plugins together so individual proof modules avoid loading the full tactic library.
-/
