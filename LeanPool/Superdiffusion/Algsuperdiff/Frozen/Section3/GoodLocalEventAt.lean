/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.GoodLocalEvents
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementTranslation

/-!
# GoodLocalEventAt

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

-- FROZEN-STATEMENT-BEGIN
/-- The local good event transported to a translated cutoff sample. -/
noncomputable def Algsuperdiff.Frozen.Section3.goodLocalEventAt
    {d : ℕ} (M : Algsuperdiff.Section3.ABKModel d) (Ccg : ℝ) (m n : ℤ)
    (z : HCPolySupport.Vec d) :
    Set (Algsuperdiff.Section3.Cutoff.CutoffSample d) :=
  Algsuperdiff.Section3.Cutoff.translateCutoffSample z ⁻¹'
    Algsuperdiff.Section3.Provider.BadEvents.goodLocalEvent M Ccg
      (HCPolySupport.originCube d m) n
-- FROZEN-STATEMENT-END
