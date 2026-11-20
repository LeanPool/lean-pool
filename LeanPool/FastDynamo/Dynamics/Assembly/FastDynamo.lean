/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate

/-!
# Dynamos, fast dynamos and slow dynamos

The notions of the paper's Section 1.1, in terms of the growth rate `γ(u, ε)` of the induction
semigroup (`gamma`, with its total extension `gammaOf` in the diffusivity):

* `IsDynamoAt`: `u` is a dynamo at diffusivity `ε` when `γ(u, ε) > 0`;
* `IsFastDynamo`: `u` is a fast dynamo when `liminf_{ε ↓ 0} γ(u, ε) > 0`;
* `IsSlowDynamo`: `u` is a slow dynamo when `γ(u, ε) > 0` for every sufficiently small `ε` and
  `γ(u, ε) → 0` as `ε ↓ 0`.

The constructed velocity `mainVelocity` is a dynamo at every `0 < ε ≤ ε₀`
(`isDynamoAt_mainVelocity`) and a fast dynamo (`isFastDynamo_mainVelocity`), the fast-dynamo
property of the paper's Theorem 1.2 (`thm:main`, `eq:main-growth-conclusion`); no fast dynamo is
a slow dynamo (`IsFastDynamo.not_isSlowDynamo`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

/-- `u` is a *dynamo at diffusivity `ε`* when its growth rate `γ(u, ε)` is positive
(Section 1.1 of the paper). -/
def IsDynamoAt (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ}
    (hε : 0 < ε) : Prop :=
  0 < gamma u hu hε

/-- `u` is a *fast dynamo* when `liminf_{ε ↓ 0} γ(u, ε) > 0` (Section 1.1 of the paper).  The
`liminf` is taken along `𝓝[>] 0` for the total extension `gammaOf` of the growth rate. -/
def IsFastDynamo (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) : Prop :=
  0 < liminf (gammaOf u hu) (𝓝[>] (0 : ℝ))

/-- `u` is a *slow dynamo* when `γ(u, ε) > 0` for every sufficiently small `ε` but
`γ(u, ε) → 0` as `ε ↓ 0` (Section 1.1 of the paper). -/
def IsSlowDynamo (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) : Prop :=
  (∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < gammaOf u hu ε) ∧ Tendsto (gammaOf u hu) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- No velocity is both a fast and a slow dynamo: the `liminf` of a function tending to `0`
is `0`. -/
theorem IsFastDynamo.not_isSlowDynamo {u : TransverseRealW1Inf}
    {hu : IsTransverseDivergenceFree u} (h : IsFastDynamo u hu) : ¬ IsSlowDynamo u hu := by
  intro hslow
  have h0 : liminf (gammaOf u hu) (𝓝[>] (0 : ℝ)) = 0 := hslow.2.liminf_eq
  exact absurd h (by rw [IsFastDynamo, h0]; exact lt_irrefl _)

/-- The constructed velocity is a dynamo at every diffusivity `0 < ε ≤ ε₀`. -/
theorem isDynamoAt_mainVelocity {ε : ℝ} (hpos : 0 < ε) (hle : ε ≤ mainEps0) :
    IsDynamoAt mainVelocity mainVelocity_isTransverseDivergenceFree hpos :=
  lt_of_lt_of_le (EReal.coe_pos.2 mainGrowthFloor_pos) (gamma_ge_gamma0 hpos hle)

/-- The constructed velocity is a fast dynamo, the content of Theorem 1.2 (`thm:main`) in the
terminology of Section 1.1. -/
theorem isFastDynamo_mainVelocity :
    IsFastDynamo mainVelocity mainVelocity_isTransverseDivergenceFree :=
  lt_of_lt_of_le (EReal.coe_pos.2 mainGrowthFloor_pos) mainGrowthFloor_le_liminf_gammaOf

end

end FastDynamo
