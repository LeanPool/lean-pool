/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn

/-!
# LInfSkewMatrixFieldOn

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- Essentially bounded matrix fields that are skew almost everywhere on a domain. -/
def Algsuperdiff.Frozen.Section24.LInfSkewMatrixFieldOn {d : ℕ}
    (U : Domain d) :=
  { h : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U //
    ∀ᵐ x ∂ volumeMeasureOn (U : Set (Vec d)), symmPart (h.1 x) = 0 }
-- FROZEN-STATEMENT-END
