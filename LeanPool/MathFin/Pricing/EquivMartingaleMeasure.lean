/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Martingales.EquivMeasure
public import LeanPool.MathFin.Probability.Martingales.MartingaleFrozen

/-!
# Equivalent martingale measures up to a horizon

`IsEMM 𝓕 P S T Q`: `Q` is an equivalent martingale measure for the discounted price `S` up to the
horizon `T`. `Q` is a probability measure with the null sets of `P`, and `S` frozen at the
horizon, `t ↦ S (min t T)`, is a `Q`-martingale for `𝓕`. Time is any linearly ordered index: the
discrete market (`FTAP.lean`, time `ℕ`) and the continuous one (`ContinuousMarket.lean`, time
`ℝ≥0`) state their theorems about this one structure. The horizon is part of the notion because a
price need not be a `Q`-martingale past it; a `Q`-martingale on all of time is an EMM at every
horizon (`IsEMM.of_martingale`).

The one-period market keeps its own `OnePeriodVector.IsEMM` (a measure under which the price
increment is centred); `isEMM_one_iff_onePeriod` (`FTAP.lean`) shows it is this notion at `T = 1`
with `𝓕 0 = ⊥`.

## Main definitions

* `IsEMM 𝓕 P S T Q`: `Q ≈ P` and `t ↦ S (min t T)` is a `Q`-martingale for `𝓕`.

## Main results

* `IsEMM.of_martingale`: a martingale under an equivalent probability measure gives an EMM at
  every horizon.
* `IsEMM.adapted`, `IsEMM.integrable`, `IsEMM.condExp_eq`: before the horizon the price is
  adapted and integrable and satisfies `Q[S t | 𝓕 s] = S s` (`martingale_min_iff`).

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981].
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied]
  (equivalent martingale measures and the fundamental theorem).

## Tags

equivalent martingale measure, risk-neutral measure, pricing measure, martingale measure,
finite horizon, MSC 60G44, MSC 60G42, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [LinearOrder ι]

/-- **Equivalent martingale measure up to the horizon `T`.** `Q` is a probability measure
mutually absolutely continuous with `P`, and the price `S` frozen at the horizon,
`t ↦ S (min t T)`, is a `Q`-martingale for `𝓕`. A `Q`-martingale on all of `ι` is an EMM at
every horizon (`IsEMM.of_martingale`). -/
structure IsEMM (𝓕 : Filtration ι m0) (P : Measure Ω) (S : ι → Ω → F) (T : ι)
    (Q : Measure Ω) : Prop extends IsEquivProbMeasure P Q where
  martingale : Martingale (fun t ↦ S (min t T)) 𝓕 Q

namespace IsEMM

variable {𝓕 : Filtration ι m0} {P Q : Measure Ω} {S : ι → Ω → F} {T : ι}

/-- **A martingale under an equivalent probability measure is an EMM at every horizon.** -/
theorem of_martingale [IsProbabilityMeasure Q] (hS : Martingale S 𝓕 Q) (hQP : Q ≪ P)
    (hPQ : P ≪ Q) (T : ι) : IsEMM 𝓕 P S T Q :=
  ⟨⟨inferInstance, hQP, hPQ⟩, martingale_min_of_martingale hS T⟩

/-- Before the horizon the price is `𝓕`-adapted. -/
theorem adapted (h : IsEMM 𝓕 P S T Q) {t : ι} (ht : t ≤ T) : StronglyMeasurable[𝓕 t] (S t) :=
  have := h.isProb
  (martingale_min_iff.mp h.martingale).1 t ht

/-- Before the horizon the price is `Q`-integrable. -/
theorem integrable (h : IsEMM 𝓕 P S T Q) {t : ι} (ht : t ≤ T) : Integrable (S t) Q :=
  have := h.isProb
  (martingale_min_iff.mp h.martingale).2.1 t ht

/-- **The martingale property before the horizon**: `Q[S t | 𝓕 s] = S s` for `s ≤ t ≤ T`. -/
theorem condExp_eq (h : IsEMM 𝓕 P S T Q) {s t : ι} (hst : s ≤ t) (ht : t ≤ T) :
    Q[S t | 𝓕 s] =ᵐ[Q] S s :=
  have := h.isProb
  ((martingale_min_iff.mp h.martingale).2.2 hst ht).symm

end IsEMM

end MathFin
