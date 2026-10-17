/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# MatrixDerivativeNorm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02

-- FROZEN-STATEMENT-BEGIN
/-- The induced first-derivative norm for the frozen sensitivity statements. -/
noncomputable def Algsuperdiff.Frozen.Section24.matrixDerivativeNorm {d : ℕ}
    (D : Vec d →L[ℝ] Mat d) : ℝ :=
  sSup (Set.range fun v : {v : Vec d // vecNorm v ≤ 1} => matrixNorm (D v.1))
-- FROZEN-STATEMENT-END
