/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Assembly.MainGrowthRate
public import LeanPool.FastDynamo.Dynamics.GrowthBoundLimit

/-!
# The paper's `γ(u, ε)` is a limit

`FastDynamo/Dynamics/Assembly/MainGrowthRate.lean` defines `gamma`, the Lean value of the
paper's maximal growth rate

```
  γ(u, ε) := lim_{t → ∞} t⁻¹ · log ‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ}
```

(`eq:semigroup-growth-rate`), as the `EReal`-valued `limsup`
`FastDynamo.StronglyContinuousSemigroup.growthBound` of the induction semigroup on
`L²_σ(T³;ℂ³)`.  `FastDynamo/Dynamics/GrowthBoundLimit.lean` proves that for every
`C₀`-semigroup on a Banach space this `limsup` is a limit (Engel–Nagel Proposition IV.2.2, the
reference the paper cites); `L²_σ(T³;ℂ³)` is a closed subspace of a Hilbert space, so the
theorem applies to `gamma` for every divergence-free velocity and every `ε > 0`.

## Contents

* `gamma_tendsto`: `t⁻¹ log ‖e^{t L_{ε,u}}‖ → γ(u, ε)` in `[−∞, ∞)`, for every `(u, ε)`.
* `gamma_ne_bot_iff`: `γ(u, ε)` is finite exactly when `‖e^{t L_{ε,u}}‖` has an exponential
  minorant (it is never `⊤`, by `gamma_ne_top`).
* `gamma_tendsto_real`: where `γ(u, ε)` is finite, the paper's definition read in `ℝ`.
* `mainGrowthFloor_le_gamma_lim`: `eq:main-growth-conclusion` in the paper's limit form at the
  constructed velocity — the growth rate is a real number `L`, sandwiched between `γ₀` and
  `‖∇⊥ u‖_∞`, which is both the value of `gamma` and the limit of `t⁻¹ log ‖e^{t L_{ε,u}}‖`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

section Limit

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/--
**The paper's growth rate is a limit** (`eq:semigroup-growth-rate`), for every divergence-free
velocity `u` and every `ε > 0`:

```
  t⁻¹ · log ‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ} → γ(u, ε)   as t → ∞,
```

in `EReal`, with `t⁻¹ log ‖e^{t L_{ε,u}}‖` read as `⊥` at the times where the operator vanishes
(`StronglyContinuousSemigroup.growthExponent`).  This is
`StronglyContinuousSemigroup.tendsto_growthExponent` at `literalInductionSemigroup`; the
`limsup` that defines `gamma` and the paper's `lim` therefore agree for every `(u, ε)`.
-/
theorem gamma_tendsto :
    Tendsto (literalInductionSemigroup u hu hε).growthExponent atTop (𝓝 (gamma u hu hε)) :=
  (literalInductionSemigroup u hu hε).tendsto_growthExponent

/--
**When `γ(u, ε)` is finite.**  The growth rate is never `⊤` (`gamma_ne_top`), and it is not `⊥`
exactly when the semigroup norm has an exponential minorant `e^{ω t} ≤ ‖e^{t L_{ε,u}}‖` at all
positive times.  This is `StronglyContinuousSemigroup.growthBound_ne_bot_iff`.
-/
theorem gamma_ne_bot_iff :
    gamma u hu hε ≠ ⊥ ↔ ∃ ω : ℝ, ∀ t : NNReal, 0 < t →
      Real.exp (ω * t) ≤ ‖(literalInductionSemigroup u hu hε).operator t‖ :=
  (literalInductionSemigroup u hu hε).growthBound_ne_bot_iff

/--
**The real-valued form.**  Where `γ(u, ε) ≠ ⊥` there is a real number `L` with

```
  γ(u, ε) = L   and   t⁻¹ · log ‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ} → L  as t → ∞,
```

which is the paper's definition `eq:semigroup-growth-rate` read verbatim in `ℝ`.  This is
`StronglyContinuousSemigroup.exists_growthBound_eq_and_tendsto`.
-/
theorem gamma_tendsto_real (hbot : gamma u hu hε ≠ ⊥) :
    ∃ L : ℝ, gamma u hu hε = (L : EReal) ∧
      Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log
        ‖(literalInductionSemigroup u hu hε).operator (Real.toNNReal t)‖) atTop (𝓝 L) :=
  (literalInductionSemigroup u hu hε).exists_growthBound_eq_and_tendsto hbot

end Limit

/--
**`eq:main-growth-conclusion` in the paper's limit form** (with the growth rate itself read
as the limit `eq:semigroup-growth-rate`).  At the constructed velocity and for every
`0 < ε ≤ ε₀` there is a *real number* `L` which

* is at least the `ε`-independent floor `γ₀` and at most `‖∇⊥ u‖_∞`,
* is the value of `gamma`, and
* is the limit of `t⁻¹ · log ‖e^{t L_{ε,u}}‖_{L²_σ → L²_σ}` as `t → ∞`.

Compared with `mainGrowthFloor_le_gamma_le_stretching` this replaces the `EReal` sandwich by a
sandwich of real numbers and adds the limit.  `gamma_ne_bot` makes `gamma_tendsto_real`
applicable, and the two sandwich bounds are `gamma_ge_gamma0` and `gamma_le_stretching` read
through the identification `gamma = L`.
-/
theorem mainGrowthFloor_le_gamma_lim {ε : ℝ} (hpos : 0 < ε) (hle : ε ≤ mainEps0) :
    ∃ L : ℝ, mainGrowthFloor ≤ L ∧ L ≤ ‖transverseStretchingCoefficient mainVelocity‖ ∧
      gamma mainVelocity mainVelocity_isTransverseDivergenceFree hpos = (L : EReal) ∧
      Tendsto (fun t : ℝ ↦ t⁻¹ * Real.log
        ‖(literalInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree
          hpos).operator (Real.toNNReal t)‖) atTop (nhds L) := by
  obtain ⟨L, hgamma, hL⟩ := gamma_tendsto_real mainVelocity
    mainVelocity_isTransverseDivergenceFree hpos (gamma_ne_bot hpos hle)
  refine ⟨L, ?_, ?_, hgamma, hL⟩
  · have h := gamma_ge_gamma0 hpos hle
    rw [hgamma] at h
    exact EReal.coe_le_coe_iff.1 h
  · have h := gamma_le_stretching mainVelocity mainVelocity_isTransverseDivergenceFree hpos
    rw [hgamma] at h
    exact EReal.coe_le_coe_iff.1 h

end

end FastDynamo
