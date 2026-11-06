/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Regularly varying sequences

Source lines 846–853: the normalizing sequence `(a_n)` is increasing and regularly varying of
index `1/α`, i.e. `a_n / n^{1/α}` is slowly varying. This directory is a pure real-analysis
toolbox about a monotone sequence `a : ℕ → ℝ`, positive at every `n ≥ 1`, that is regularly
varying of an index `ρ` (for the paper `ρ = 1/α ∈ [1/2, 1)`).

The sequential form of regular variation used here is

  `a ⌊c n⌋ / a n → c ^ ρ` for every `c > 0`.

The bridge from the paper's formulation (`x ↦ a_{⌊x⌋} / x^ρ` is slowly varying in the sense of
`PoissonDeclumping.SlowlyVarying`) is `PoissonDeclumping.RegularlyVaryingSeq.of_slowlyVarying`
in `PoissonDeclumping.RegularVariation.Bridge`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PoissonDeclumping

/-- A real sequence `a` is regularly varying of index `ρ` (sequential form):
`a ⌊c n⌋₊ / a n → c ^ ρ` as `n → ∞`, for every `c > 0`. -/
def RegularlyVaryingSeq (ρ : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => a ⌊c * n⌋₊ / a n) atTop (𝓝 (c ^ ρ))

end PoissonDeclumping
