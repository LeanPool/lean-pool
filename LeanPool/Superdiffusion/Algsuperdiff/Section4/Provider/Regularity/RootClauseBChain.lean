/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBInputs

/-!
# RootClauseBChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The composite prefactor -/

/-- The Step-7c gradient-display constant `C_g = 3^{3d+1/4}·C_cacc·(C_osc√C_lam+1)`
of `StepSevenCaccFinalDisplay`. -/
def rootClauseBCg (d : ℕ) (Ccacc Cosc CBc : ℝ) : ℝ :=
  Real.rpow (3 : ℝ) (3 * (d : ℝ) + 1 / 4) * Ccacc *
    (Cosc * Real.sqrt (256 / 63 * CBc) + 1)

/-- **The clause-(B) prefactor**, the composite constant the outer collapse
produces: the oscillation half's `C_g√C_cmp·(embedding·bridge·Poincaré·C_tr)`
plus the data half's `C_g(√C_cmp·C_WG + C_dM)`, at `C_cmp = 4`. -/
def rootClauseBPrefactor (d : ℕ) [NeZero d] (Cch Ccacc Cosc CBc CB Ctr CWG CdM : ℝ) : ℝ :=
  rootClauseBCg d Ccacc Cosc CBc * Real.sqrt 4 *
      (Real.sqrt ((3 : ℝ) ^ d) * stepSevenEmbeddingConst d *
        stepSevenBridgeConst stepSevenCgS *
        (Cch * 64 * (Real.sqrt (32 / 7 * CB) + 32 / 7 * CB)) * Ctr) +
    rootClauseBCg d Ccacc Cosc CBc * (Real.sqrt 4 * CWG + CdM)

/-! ## 2. Two scalar steps -/

/-- The final constant enlargement (`RootAssemblyParameters` §3's pattern). -/
theorem clauseB_const_mono {A P Cest R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hP : P ≤ Cest) (h : A ≤ P * R * T) : A ≤ Cest * R * T := by
  have h1 : P * R ≤ Cest * R := mul_le_mul_of_nonneg_right hP hR
  have h2 : P * R * T ≤ Cest * R * T := mul_le_mul_of_nonneg_right h1 hT
  linarith only [h, h2]

end

end Algsuperdiff.Section4.Provider.Regularity
