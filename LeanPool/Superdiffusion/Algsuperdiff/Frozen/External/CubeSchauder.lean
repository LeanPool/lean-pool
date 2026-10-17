/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderSeal

/-!
# CubeSchauder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support

-- External classical input.  ABK26 asserts "By Schauder estimates for the Poisson
-- equation in a cube (by odd reflection)" with no citation and no in-paper proof; this
-- file states the estimate actually used, and it is proved in this repository.
-- The estimate is the global gradient Hoelder bound for the CONSTANT-coefficient
-- Dirichlet problem  -sigma Delta v = div g  in  cube_m,  v = h  on the boundary, with
-- divergence-form data g in C^{0,1/2} and datum gradient in L^infty cap C^{0,1/2} -- pure
-- constant-coefficient elliptic regularity on the comparator side (flat-legitimate: the
-- Delta-comparator and pure data), no random environment, no nu, no coarse quantity.  The
-- statement bundles EXISTENCE of the solution with the regularity of ITS OWN gradient
-- representative, so no continuous-representative bookkeeping leaks to the consumer; the
-- Dirichlet solution is unique (zero-trace difference + the weak equation), so this is the
-- solution.  Carriers: the repository's Support layer (IsDirichletSolutionOn,
-- HolderSeminormBoundOn) over CoarseGraining's H1Function/openCubeSet/originCube; the left-hand
-- gauge
-- and the right-hand data bracket are spelled in primitives (the provider definitions
-- wsInftyGauge/dataBracket unfold to exactly these terms at Q = originCube d m).  The
-- constant depends on (d, s) only -- uniform in m (scaling), sigma (linearity), g, h.
-- Range s in (0, 1/2]: strictly below the convex-corner regularity ceiling of the cube.

-- FROZEN-STATEMENT-BEGIN
theorem Algsuperdiff.Frozen.External.cube_schauder
    {d : ℕ} (dimension : 2 ≤ d)
    (s : ℝ) (s_pos : 0 < s) (s_le : s ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (sigma : ℝ), 0 < sigma →
        ∀ (g : Vec d → Vec d) (h : H1Function (openCubeSet (originCube d m)))
          (Kg KhInf Kh : ℝ),
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
          (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
          HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
          ∃ v : H1Function (openCubeSet (originCube d m)),
            IsDirichletSolutionOn (fun _ => sigma • (1 : Mat d)) (originCube d m) v h g ∧
            ∃ Ksup KHol : ℝ, 0 ≤ Ksup ∧ 0 ≤ KHol ∧
              (∀ x ∈ openCubeSet (originCube d m), ‖v.grad x‖ ≤ Ksup) ∧
              HolderSeminormBoundOn (openCubeSet (originCube d m)) s KHol v.grad ∧
              Real.rpow 3 (-(s * (m : ℝ))) * Ksup + KHol ≤
                C * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
                  (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                    (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh))
-- FROZEN-STATEMENT-END
    := by
  have : NeZero d := ⟨by omega⟩
  exact Algsuperdiff.Section4.Provider.Schauder.cube_schauder_of_zeroDatumCubeSchauder
    (Algsuperdiff.Section4.Provider.Schauder.zeroDatumRouteConst_nonneg d
      (Algsuperdiff.Section4.Provider.Schauder.zeroDatumCampanatoConst_nonneg d))
    Algsuperdiff.Section4.Provider.Schauder.zeroDatumCubeSchauder_unconditional
    dimension s s_pos s_le
