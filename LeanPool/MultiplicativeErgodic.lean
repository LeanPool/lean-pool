/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Auerbach
public import LeanPool.MultiplicativeErgodic.Grassmannian
public import LeanPool.MultiplicativeErgodic.GrowthFunction
public import LeanPool.MultiplicativeErgodic.DetGrowth
public import LeanPool.MultiplicativeErgodic.MeasurableSelection
public import LeanPool.MultiplicativeErgodic.GrassmannianContraction
public import LeanPool.MultiplicativeErgodic.StrongMeasurability
public import LeanPool.MultiplicativeErgodic.NonAtomic
public import LeanPool.MultiplicativeErgodic.Rokhlin
public import LeanPool.MultiplicativeErgodic.Tempered
public import LeanPool.MultiplicativeErgodic.SlowProjection
public import LeanPool.MultiplicativeErgodic.Induction
public import LeanPool.MultiplicativeErgodic.Birkhoff
public import LeanPool.MultiplicativeErgodic.Kingman
public import LeanPool.MultiplicativeErgodic.BalancedKingman
public import LeanPool.MultiplicativeErgodic.Cocycle
public import LeanPool.MultiplicativeErgodic.Existence
public import LeanPool.MultiplicativeErgodic.Main
public import LeanPool.MultiplicativeErgodic.Appendix
public import LeanPool.MultiplicativeErgodic.CompactnessIndex
public import LeanPool.MultiplicativeErgodic.MainCompactness
public import LeanPool.MultiplicativeErgodic.Uniqueness
public import LeanPool.MultiplicativeErgodic.Backward

/-!
# Oseledets decomposition by subspace growth estimates

Source: doi:10.1090/btran/146, url:https://gitlab.com/georgelee/vibemet
Authors: George Lee
Status: verified
Main declarations: `MultiplicativeErgodic.mainres`,
  `MultiplicativeErgodic.mainres_compactnessIndex`, `MultiplicativeErgodic.kingman`,
  `MultiplicativeErgodic.grassmannianFin_complete`
Tags: ergodic-theory, lyapunov-exponents, banach-spaces, grassmannians, subadditivity
MSC: 37H15, 37A30, 46B20
-/
