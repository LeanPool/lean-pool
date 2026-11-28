/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.Call

/-!
# Probabilistic interpretation of `bsd2`: the exercise-probability identity

The BS formula `bsV = S · Φ(d_1) − K · e^{−rT} · Φ(d_2)` has two `Φ` values.
Each has a probabilistic meaning under the risk-neutral measure `Q`:

* `Φ(d_2) = Q(S_T > K)` — the risk-neutral exercise probability.
* `Φ(d_1) = Q^{(S)}(S_T > K)` — the same probability under the
  **stock-numeraire measure** (change of numeraire), formalised in the
  companion `StockNumeraire.lean` (`stockNumeraire_exercise_probability`).

This file formalises the simpler `Φ(d_2) = Q(S_T > K)` identity. It is the
probabilistic content of `bsd2`: a parameter that arises algebraically in
the BS formula is identified with the risk-neutral probability of finishing
in the money.

## Why this is "first principles"

Existing library content treats `bsd2` as a closed-form expression
(`d_2 := (log(S_0/K) + (r − σ²/2)T) / (σ√T)`). This file gives `bsd2` its
*probabilistic meaning*: it is the negative of the standardised
log-moneyness threshold, and `Φ(bsd2)` is the risk-neutral exercise
probability.

The companion `Φ(d_1) = Q^{(S)}(S_T > K)` identity — via the change-of-
numeraire machinery (Radon-Nikodym derivative of the stock-numeraire
measure w.r.t. the risk-neutral measure) — is formalised in
`StockNumeraire.lean` (`stockNumeraire_exercise_probability`).

## Building blocks (all pre-existing in `Models.BlackScholes.Call`)

* `BSCallHyp` — the risk-neutral law specification: `Z ~ N(0, 1)` under `Q`,
  `S_T = bsTerminal S_0 r σ T (Z ·)`.
* `bsTerminal_gt_K_iff` — exercise-region identification:
  `S_T(z) > K ↔ z > −bsd2 S_0 K r σ T`.
* `gaussianReal_Ioi_toReal` — right-tail probability:
  `(gaussianReal 0 1 (Ioi a)).toReal = Φ(−a)`.

## Main results

* `riskNeutralProb_S_T_gt_K`: `Q(S_T > K) = Φ(bsd2 S_0 K r σ T)`. The
  probabilistic interpretation of `Φ(d_2)` in the BS formula.

## Tags

risk-neutral exercise probability, in-the-money probability, d2 interpretation, Black–Scholes,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-- **Risk-neutral exercise probability identification**: under the risk-
neutral hypothesis `BSCallHyp`, the probability that the terminal asset
`S_T` exceeds the strike `K` equals `Φ(bsd2 S_0 K r σ T)`.

Proof: the exercise region `{S_T(z) > K}` is identified with
`{z > −bsd2}` by `bsTerminal_gt_K_iff`. The risk-neutral probability of
this set is `Q(Z > −bsd2)`, which by `HasLaw` transfer equals
`(gaussianReal 0 1)(Ioi (−bsd2))`. By `gaussianReal_Ioi_toReal`, this is
`Φ(−(−bsd2)) = Φ(bsd2)`. -/
theorem riskNeutralProb_S_T_gt_K
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ T : ℝ} {Z : Ω → ℝ}
    (h : BSCallHyp Q S_0 K r σ T Z) :
    (Q {ω | bsTerminal S_0 r σ T (Z ω) > K}).toReal =
      Phi (bsd2 S_0 K r σ T) := by
  obtain ⟨hS_0, hK, hσ, hT, hZ⟩ := h
  -- Identify the exercise region with {Z > -d_2}.
  have h_set_eq :
      {ω | bsTerminal S_0 r σ T (Z ω) > K} = Z ⁻¹' Set.Ioi (-bsd2 S_0 K r σ T) := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
    exact bsTerminal_gt_K_iff hS_0 hK hσ hT (Z ω)
  rw [h_set_eq]
  -- HasLaw transfer: Q (Z ⁻¹' A) = (Q.map Z) A = (gaussianReal 0 1) A.
  have h_meas : AEMeasurable Z Q := hZ.aemeasurable
  rw [← Measure.map_apply_of_aemeasurable h_meas measurableSet_Ioi]
  rw [hZ.map_eq]
  -- (gaussianReal 0 1)(Ioi a).toReal = Φ(-a). With a = -d_2, Φ(-(-d_2)) = Φ(d_2).
  rw [gaussianReal_Ioi_toReal]
  congr 1; ring

end MathFin
