/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

-- Background
public import LeanPool.AbstractLinearControl.Background.Semigroup
public import LeanPool.AbstractLinearControl.Background.Lp
public import LeanPool.AbstractLinearControl.Background.Phillips
public import LeanPool.AbstractLinearControl.Background.InvariantHahnBanach
-- Definitions 1.1 and 1.4, Lemma 2.1
public import LeanPool.AbstractLinearControl.Definitions
-- Proposition 1.3
public import LeanPool.AbstractLinearControl.ContinuityFiniteP
-- Theorem 1.5
public import LeanPool.AbstractLinearControl.ZeroClass
-- Corollary 1.6
public import LeanPool.AbstractLinearControl.ContinuityLinfty
-- Section 3: examples
public import LeanPool.AbstractLinearControl.Examples.FinitePNotZeroClass
public import LeanPool.AbstractLinearControl.Examples.ExoticMean
public import LeanPool.AbstractLinearControl.Examples.Periodization
public import LeanPool.AbstractLinearControl.Examples.NoRepresentation

/-!
# Continuity and zero-class properties of abstract linear control systems

Source: url:https://github.com/frederic-marbach/alcs/tree/bda56576f8b2730b73a55f273511c80fabbe56f4
Authors: Frédéric Marbach, GPT-6 Pro, Claude Opus 5.5
Status: verified
Main declarations: `AbstractLinearControl.ALCS.zero_class`
Tags: functional-analysis, control-theory, semigroups, lp-spaces, hahn-banach
MSC: 47D06, 93C25, 46E30
-/
