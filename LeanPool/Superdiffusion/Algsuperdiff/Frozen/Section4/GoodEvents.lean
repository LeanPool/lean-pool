/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# GoodEvents

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

/-!
# The translated good event — [ABK] `d.good.event.for.lambda`

`goodEventAt M Ccg m y s ep` is the good event of the coarse-graining scheme
at scale `m`, seen from the base point `y`: the pullback of the centred good
event along the translation of the cutoff sample by `y`.  The parameters `s`
and `ep` are the fractional exponent and the smallness level.

Definition; no proof obligation.
-/

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Section4.goodEventAt
    {d : ℕ} (M : Algsuperdiff.Section3.ABKModel d) (Ccg : ℝ) (m : ℤ)
    (y : HCPolySupport.Vec d) (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    Set (Algsuperdiff.Section3.Cutoff.CutoffSample d) :=
  Algsuperdiff.Section3.Cutoff.translateCutoffSample y ⁻¹'
    Algsuperdiff.Section4.Support.goodEventBase M Ccg m s ep
-- FROZEN-STATEMENT-END
