/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.DeGiorgiOneSidedTwo
public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.Stampacchia.DeGiorgiCore

/-!
# DeGiorgiOneSided

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Dimension-complete one-sided De Giorgi core

This file joins the local two-dimensional endpoint to the upstream core for
dimensions at least three.
-/

namespace DivergenceFormProcess.Regularity

open HCPolySupport MeasureTheory

/-- The one-sided De Giorgi core in every dimension at least two. -/
theorem deGiorgi_one_sided_core_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (z : Vec d) (L : ℝ), 0 < L →
        ∀ (w₁ w₂ : H1Function (axisCube z L)),
          Measurable w₁.toFun → Measurable w₂.toFun →
          MemH10 (axisCube z L) (fun x => w₁.toFun x - w₂.toFun x) →
          ∀ (m₀ E₀ : ℝ), 0 ≤ E₀ →
          MeasureTheory.volume {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x} +
              MeasureTheory.volume {x | x ∈ axisCube z L ∧ m₀ < w₂.toFun x} ≤
            MeasureTheory.volume (axisCube z L) →
          (∀ k : ℝ, 0 ≤ k →
            (∑ i : Fin d, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator
                  (fun x => w₁.grad x i)) 2
                (volumeMeasureOn (axisCube z L))).toReal) +
              ∑ i : Fin d, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator
                  (fun x => w₂.grad x i)) 2
                (volumeMeasureOn (axisCube z L))).toReal ≤
              E₀ * Real.sqrt
                ((MeasureTheory.volume
                    {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
                  (MeasureTheory.volume
                    {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) →
          ∀ᵐ x ∂(volumeMeasureOn (axisCube z L)),
            w₁.toFun x ≤ m₀ + Cd * L * E₀ := by
  rcases eq_or_lt_of_le hd with hdim | hdim
  · subst d
    exact deGiorgi_one_sided_core_two
  · exact HCPolySupport.deGiorgi_one_sided_core (by omega)

end DivergenceFormProcess.Regularity
