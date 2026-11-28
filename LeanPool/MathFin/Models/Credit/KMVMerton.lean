/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.GarmanNormalForm

/-!
# KMV-Merton structural credit (as a Garman-form specialisation)

In the Merton (1974) / KMV structural credit-risk model, the firm's asset
value `V_t` follows the same lognormal dynamics as a Black-Scholes asset,
and default occurs at maturity `T` if `V_T < F` (face debt). Under the
risk-neutral measure, the **distance to default** at time `0` is the BS
`d_2` parameter with `V_0` as spot and `F` as strike, and the **risk-neutral
probability of default** is `Φ(−d_2)`.

The structural insight: this is *not* a separate pricing model. Default-or-
not is the same Φ(d_2) that prices the cash-or-nothing digital option on
the firm's asset value. KMV-Merton is the **Garman normal form** of BS
applied with firm value as the asset and face debt as the strike:

  `Distance to default = gbsd2 V F (e^{−rT}) σ_V T`.

This file used to alias `kmvDistanceToDefault := bsd2`, recording the same
fact under three different names. We now make the Garman connection
explicit (the unifying structural insight) and keep only the substantive
PD-as-probability bounds.

## Main definitions

* `kmvDistanceToDefault`: the distance to default in Garman normal form,
  `d₂ = gbsd2 V F (e^{−rT}) σ_V T`, with the firm value as spot and the face debt as strike.
* `kmvPD`: the risk-neutral probability of default `Φ(−d₂)` at maturity `T`.

## Main results

* `kmvDistanceToDefault_eq_bsd2`: equivalence to the BS `bsd2` (this is
  the *structural identity*, the same `d_2` from BS).
* `kmvPD_nonneg`, `kmvPD_le_one`: probability bounds.
* `kmv_survival_eq_Phi_d2`: `1 − PD = Φ(d_2)`.

## Tags

Merton model, KMV, distance to default, structural credit model, default probability, firm value,
MSC 91G40, JEL G33, JEL G12
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Distance to default** in the KMV-Merton model, expressed in Garman normal
form: `d_2 = gbsd2 V F (e^{−rT}) σ_V T` with firm value `V` and face debt `F`.

The Garman form makes the structural connection explicit: this is the *same*
`d_2` as the BS call formula, instantiated with credit-risk variables. -/
noncomputable def kmvDistanceToDefault (V_0 F r σ_V T : ℝ) : ℝ :=
  gbsd2 V_0 F (Real.exp (-(r * T))) σ_V T

/-- **The KMV distance-to-default equals the BS `d_2`** at the standard
parameters. This is *not* a new formula — it is the BS `d_2`, in different
variable names. -/
theorem kmvDistanceToDefault_eq_bsd2 (V_0 F r σ_V T : ℝ) (hV : 0 < V_0) (hF : 0 < F) :
    kmvDistanceToDefault V_0 F r σ_V T = bsd2 V_0 F r σ_V T := by
  unfold kmvDistanceToDefault
  rw [bsd2_eq_gbsd2_standard V_0 F r σ_V T hV hF]

/-- **Risk-neutral probability of default** at maturity `T`. The same Φ(−d_2)
that prices the cash-or-nothing put on the firm value. -/
noncomputable def kmvPD (V_0 F r σ_V T : ℝ) : ℝ :=
  Phi (-(kmvDistanceToDefault V_0 F r σ_V T))

/-- **PD ≥ 0** (Φ takes non-negative values). -/
lemma kmvPD_nonneg (V_0 F r σ_V T : ℝ) : 0 ≤ kmvPD V_0 F r σ_V T :=
  Phi_nonneg _

/-- **PD ≤ 1** (`Φ` takes values in `[0,1]`; `Phi_le_one` from `StandardNormal`). -/
lemma kmvPD_le_one (V_0 F r σ_V T : ℝ) : kmvPD V_0 F r σ_V T ≤ 1 :=
  Phi_le_one _

/-- **Survival = 1 − PD = Φ(d_2)**: the risk-neutral probability of no default. -/
theorem kmv_survival_eq_Phi_d2 (V_0 F r σ_V T : ℝ) :
    1 - kmvPD V_0 F r σ_V T = Phi (kmvDistanceToDefault V_0 F r σ_V T) := by
  unfold kmvPD
  have := Phi_add_Phi_neg (kmvDistanceToDefault V_0 F r σ_V T)
  linarith

end MathFin
