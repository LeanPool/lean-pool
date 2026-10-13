/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.CompactOpen

/-!
# ShellField

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open scoped Matrix.Norms.Elementwise

-- FROZEN-STATEMENT-BEGIN
noncomputable def Algsuperdiff.Frozen.Assumptions.ShellField (d : ℕ) :=
  { p :
      ContinuousMap (HCPolySupport.Vec d) (HCPolySupport.Mat d) ×
        (ContinuousMap (HCPolySupport.Vec d)
            (HCPolySupport.Vec d →L[ℝ] HCPolySupport.Mat d) ×
          ContinuousMap (HCPolySupport.Vec d)
            (HCPolySupport.Vec d →L[ℝ]
              (HCPolySupport.Vec d →L[ℝ] HCPolySupport.Mat d))) //
    (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧
      (∀ x, HasFDerivAt p.2.1 (p.2.2 x) x) ∧
      ∀ x i j, p.1 x i j = -p.1 x j i }
-- FROZEN-STATEMENT-END
