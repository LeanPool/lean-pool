/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.MeanInequalities

/-!
# BoundaryStrip

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the boundary-strip volume fraction

The proof of `l.approximation.stationary.by.local` in ABK26 fixes a cutoff
`η_{K,L}` that equals `1` at distance at least `3^{K-L}` from `∂cu_K`, sets

`Σ_{K,L} := {x ∈ cu_K : η_{K,L}(x) ≠ 1}`,

and records the volume fraction `e.boundary.strip.volume`

`|Σ_{K,L}| ≤^{-L} |cu_K|`.

With the concentric-subcube cutoffs of CoarseGraining
(`Homogenization.QuantitativeCubeCutoff`, which is `1` on `scaledClosedCubeSet
Q ρ` and supported in `scaledOpenCubeSet Q 1`) the set `Σ` is contained in
`cu_K \ scaledClosedCubeSet cu_K ρ` with `ρ = 1 - 3^{-L}`, whose volume
fraction is exactly `1 - ρ^d`.  So the displayed estimate reduces to the
elementary Bernoulli bound `1 - ρ^d ≤ d (1 - ρ)`, with `C = d`.

This file proves that scalar reduction, which is the only part of
`e.boundary.strip.volume` that is independent of the cube-measure A.
-/

namespace Algsuperdiff.Section3.Provider.Corrector

/-- Bernoulli's inequality in the form used for the boundary strip: for
nonnegative `ρ` the missing volume fraction of a concentric subcube of ratio `ρ`
in dimension `n` is at most `n (1 - ρ)`. -/
theorem one_sub_pow_le_mul_one_sub (n : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) :
    1 - ρ ^ n ≤ (n : ℝ) * (1 - ρ) := by
  have hbase : (-2 : ℝ) ≤ ρ - 1 := by linarith
  have hpow : 1 + (n : ℝ) * (ρ - 1) ≤ (1 + (ρ - 1)) ^ n :=
    one_add_mul_le_pow hbase n
  have hsimp : (1 : ℝ) + (ρ - 1) = ρ := by ring
  rw [hsimp] at hpow
  nlinarith [hpow]

end Algsuperdiff.Section3.Provider.Corrector
