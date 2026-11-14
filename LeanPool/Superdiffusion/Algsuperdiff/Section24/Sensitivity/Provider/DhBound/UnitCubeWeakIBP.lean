/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.DhBound.WeakIBP
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity

/-!
# UnitCubeWeakIBP

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak integration by parts at the frozen unit-cube carrier

Source: ABK26 (`e.sensitivity.basic.split`), specialized to the frozen
sensitivity carrier of `l.Dh.bound`.

The general weak integration by parts
(`integral_grad_dot_matVecMul_grad_eq_neg_of_hasWeakDeriv`) is discharged at
the `UnitCubeSkewW2Infinity` perturbation: the antisymmetry,
`L∞` control, and weak-derivative premises are all supplied by the frozen
structure fields, so the resulting statement carries no analytic side
conditions beyond the `H¹₀` membership of the test function — the exact
zero-trace input demanded by the source display.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.DhBound

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The weak first-derivative data of a frozen unit-cube perturbation, in the
`matWeakDiv` packaging: `unitCubeDerivData h k x i j = ∂_k h_{ij} (x)`. -/
def unitCubeDerivData (h : UnitCubeSkewW2Infinity d) :
    Fin d → Vec d → Mat d :=
  fun k x => h.firstDeriv x (basisVec k)

end

end Algsuperdiff.Section24.Sensitivity.Provider.DhBound
