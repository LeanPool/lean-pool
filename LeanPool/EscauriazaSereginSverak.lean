/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Escauriaza–Seregin–Šverák and Ladyzhenskaya–Prodi–Serrin regularity

Source: url:https://github.com/scottnarmstrong/EscauriazaSereginSverak/tree/ae1a0e46086b9b16179dea76b41da10b01845151
Authors: Scott Armstrong
Status: verified
Main declarations: `ESS.essSmooth`, `ESS.ladyzhenskayaProdiSerrin`, `ESS.serrinCriterion`
Tags: Navier–Stokes, partial differential equations, regularity, unique continuation
MSC: 35Q30, 35B65, 35B60
-/

module

public import LeanPool.EscauriazaSereginSverak.Statements.BackwardUniqueness
public import LeanPool.EscauriazaSereginSverak.Statements.CarlemanGaussian
public import LeanPool.EscauriazaSereginSverak.Statements.CarlemanHalfSpace
public import LeanPool.EscauriazaSereginSverak.Statements.EssGlobal
public import LeanPool.EscauriazaSereginSverak.Statements.EssL5Unique
public import LeanPool.EscauriazaSereginSverak.Statements.EssLocal
public import LeanPool.EscauriazaSereginSverak.Statements.EssSmooth
public import LeanPool.EscauriazaSereginSverak.Statements.LadyzhenskayaProdiSerrin
public import LeanPool.EscauriazaSereginSverak.Statements.SerrinCriterion
public import LeanPool.EscauriazaSereginSverak.Statements.UniqueContinuation
