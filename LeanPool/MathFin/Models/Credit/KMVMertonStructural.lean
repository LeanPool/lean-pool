/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Credit.KMVMerton
public import LeanPool.MathFin.Models.BlackScholes.RiskNeutralProbabilities

/-!
# KMV-Merton structural model: probabilistic content of `kmvPD`

The pre-existing `Models/Credit/KMVMerton.lean` defines `kmvPD := Phi(−kmvDD)`
and proves the algebraic survival identity `1 − kmvPD = Phi(kmvDD)`. The
*probabilistic content* — namely, that `kmvPD` is the actual risk-neutral
probability of default `Q({V_T ≤ F})` — was previously stated only in the
docstring.

This file proves the connection rigorously using `riskNeutralProb_S_T_gt_K`
from `Models/BlackScholes/RiskNeutralProbabilities.lean`. With firm asset value
`V_T = bsTerminal V_0 r σ_V T (Z ·)` under the risk-neutral measure `Q` and
debt face `F`, the no-default probability is

  `Q({V_T > F}) = Phi(bsd2 V_0 F r σ_V T) = 1 − kmvPD`,

so default probability `Q({V_T ≤ F}) = kmvPD = Phi(−bsd2)`.

The structural identity **equity = call on firm assets** (Merton 1974) needs no theorem of its
own: limited liability makes the equity payoff `max(V_T − F, 0)`, so its discounted risk-neutral
value is `bs_call_formula` read with `(S_0, K, σ) ↦ (V_0, F, σ_V)`.

## Main results

* `kmvPD_eq_one_sub_survival_probability`: connects `kmvPD` to the actual
  risk-neutral probability `Q({V_T > F})`.

## References

* [R. C. Merton, *On the pricing of corporate debt: the risk structure of interest
  rates*][Merton1974]

## Tags

Merton model, KMV, risk-neutral default probability, structural credit model, equity as call option,
distance to default, MSC 91G40, MSC 91G20, JEL G33
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **KMV-Merton default probability identification**: under the BS lognormal
hypothesis for firm asset value `V_T = bsTerminal V_0 r σ_V T (Z ·)`,

  `kmvPD V_0 F r σ_V T = 1 − Q({ω | V_T(ω) > F}).toReal`.

The RHS is *one minus the risk-neutral survival probability*. Combined with
`riskNeutralProb_S_T_gt_K`, this gives `kmvPD` the genuine probabilistic
interpretation it was advertised to have. -/
theorem kmvPD_eq_one_sub_survival_probability
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V_0 F r σ_V T : ℝ} {Z : Ω → ℝ}
    (hV : 0 < V_0) (hF : 0 < F)
    (h : BSCallHyp Q V_0 F r σ_V T Z) :
    kmvPD V_0 F r σ_V T =
      1 - (Q {ω | bsTerminal V_0 r σ_V T (Z ω) > F}).toReal := by
  rw [riskNeutralProb_S_T_gt_K h]
  rw [← kmvDistanceToDefault_eq_bsd2 V_0 F r σ_V T hV hF]
  have := kmv_survival_eq_Phi_d2 V_0 F r σ_V T
  linarith

/-- **KMV-Merton survival probability closed form**: under the BS lognormal
hypothesis for the firm asset value `V_T = bsTerminal V_0 r σ_V T (Z ·)`, the
risk-neutral survival (no-default) probability *is* `Φ` of the distance to
default:

  `Q({ω | V_T(ω) > F}).toReal = Phi (kmvDistanceToDefault V_0 F r σ_V T)`.

This is the genuinely probabilistic survival statement — it computes the
measure of the no-default event itself through the lognormal tail
(`riskNeutralProb_S_T_gt_K`), not merely the CDF symmetry
`1 − Φ(−DD) = Φ(DD)` recorded in `KMVMerton.lean`. Complements
`kmvPD_eq_one_sub_survival_probability` (the PD identification) with the
closed form on the survival side. -/
theorem survival_probability_eq_Phi_distanceToDefault
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {V_0 F r σ_V T : ℝ} {Z : Ω → ℝ}
    (hV : 0 < V_0) (hF : 0 < F)
    (h : BSCallHyp Q V_0 F r σ_V T Z) :
    (Q {ω | bsTerminal V_0 r σ_V T (Z ω) > F}).toReal =
      Phi (kmvDistanceToDefault V_0 F r σ_V T) := by
  rw [riskNeutralProb_S_T_gt_K h, kmvDistanceToDefault_eq_bsd2 V_0 F r σ_V T hV hF]

end MathFin
