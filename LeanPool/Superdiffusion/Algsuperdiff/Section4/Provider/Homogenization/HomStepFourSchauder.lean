/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.External.CubeSchauder
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourEnergy

/-!
# HomStepFourSchauder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the `hSch` discharge off the external Schauder input

## What this is

The definitional bridge from the external classical input
`Algsuperdiff.Frozen.External.cube_schauder` (proved internally in
this repository) to the three Schauder slots of
`stepFourEnergyDisplay`/`stepFourEnergyEndpoint`: the comparator's existence,
the gradient sup bound `hb`, the gradient Hölder bound `hH`, and the gauge
estimate `hSch` — with the constant `Csch = C(d, s)` produced ONCE, before the
scale `m`, the diffusivity `sigma` and the data, so the consumer's constant
scope is the external's own.

The inequality transfer is definitional: `wsInftyGauge (originCube d m)` and
`dataBracket` unfold to exactly the primitive terms of the external's
conclusion (the cube's scale is `m` by `rfl`).

## Axiom status

The external input is proved, with axioms exactly `[propext,
Classical.choice, Quot.sound]` and no `sorryAx`, so every consumer of this
module sees the standard axiom triple only.
-/

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-- **The comparator with its Schauder package, off the external input.**

One constant `Csch(d, s)` for every scale, diffusivity and admissible data:
the solution `v` of `-sigma Δv = ∇·g`, `v = h` on `∂□_m`, exists with its own
gradient representative bounded (`hb`), `s`-Hölder (`hH`), and gauge-controlled
by the data bracket (`hSch`) — the three slots of `stepFourEnergyEndpoint`. -/
theorem exists_comparator_schauder_package (dimension : 2 ≤ d)
    {s : ℝ} (s_pos : 0 < s) (s_le : s ≤ 1 / 2) :
    ∃ Csch : ℝ, 0 < Csch ∧
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
              wsInftyGauge (originCube d m) s Ksup KHol ≤
                Csch * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
                  dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  obtain ⟨C, hC, H⟩ := Algsuperdiff.Frozen.External.cube_schauder dimension s s_pos s_le
  refine ⟨C, hC, fun m sigma hsigma g h Kg KhInf Kh hKg hKhInf hKh => ?_⟩
  obtain ⟨v, hsol, Ksup, KHol, hKsup, hKHol, hb, hH, hgauge⟩ :=
    H m sigma hsigma g h Kg KhInf Kh hKg hKhInf hKh
  exact ⟨v, hsol, Ksup, KHol, hKsup, hKHol, hb, hH, hgauge⟩

end

end Algsuperdiff.Section4.Provider.Homogenization
