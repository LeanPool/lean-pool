/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.PDE.NeumannRHS
public import LeanPool.HighContrastHomogenization.Support.Multiscale.NormalizedNorms
public import LeanPool.Superdiffusion.Support.Sobolev.Foundations.CubeCalderonZygmund.DirichletNeumannEndpoint

/-!
# CalderonZygmund

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open HCPolySupport MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.External.calderon_zygmund
    {d : ℕ} (dimension : 2 ≤ d)
    (p : ℝ≥0∞) (one_lt_p : 1 < p) (p_lt_top : p < ∞) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (f : Vec d → Vec d),
        MemLp f p (normalizedCubeMeasure Q) →
          (∀ u : H10Function (openCubeSet Q),
              IsZeroTraceDirichletRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet Q) u (fun x => -f x) →
                MemLp u.toH1Function.grad p
                    (normalizedCubeMeasure Q) ∧
                  cubeLpNorm Q p u.toH1Function.grad ≤
                    C * cubeLpNorm Q p f) ∧
          (∀ u : H1MeanZeroFunction (openCubeSet Q),
              IsMeanZeroNeumannRhsWeakSolution
                  (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                  (openCubeSet Q) u (fun x => -f x) →
                MemLp u.toH1Function.grad p
                    (normalizedCubeMeasure Q) ∧
                  cubeLpNorm Q p u.toH1Function.grad ≤
                    C * cubeLpNorm Q p f)
-- FROZEN-STATEMENT-END
    := by
  exact HCPolySupport.CubeCalderonZygmund.exists_cubeDirichletNeumannDivergence_cz
    dimension p one_lt_p p_lt_top
