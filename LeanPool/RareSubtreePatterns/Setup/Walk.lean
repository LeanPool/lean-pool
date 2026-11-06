/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Defs

/-!
# The Łukasiewicz walk and the stable-domain hypothesis `(H_α)`

Source lines 174–181, 699–713, 719–730, 842–853. The walk has i.i.d. steps `X_i` with
`P(X_1 = i) = μ_{i+1}` for `i ≥ -1`, and `Ψ_m(i) = P(S_m = i)`.

The standing hypothesis `(H_α)` ("`μ` is critical and in the domain of attraction of an
`α`-stable law, `α ∈ (1,2]`, with `μ_1 ≠ 1`") is expressed through normalized weak
convergence: `(K_1+…+K_n−n)/a_n` converges in distribution to the law `ν`
with Laplace exponent `∫ e^{-λ y} dν = e^{λ^α}`. The separately cited truncated-moment
characterization is not included as a redundant assumption. The normalizing sequence `a` is part
  of the
data because Assumption (S) mentions `a_n`.

The definitions `stepLaw`, `walkLaw`, `SlowlyVarying`, `StableDomain` and `InStableDomain` are
in `PoissonDeclumping.Statements.Defs` (shared verbatim with `Challenge.lean`); this module adds
`walkProb`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace PoissonDeclumping

/-- `Ψ_m(i) = P(S_m = i)`, with the paper's convention `Ψ_m(i) = 0` for negative `m`. -/
noncomputable def walkProb (μ : PMF ℕ) (m : ℤ) (i : ℤ) : ℝ :=
  if 0 ≤ m then (walkLaw μ m.toNat).real {i} else 0

end PoissonDeclumping
