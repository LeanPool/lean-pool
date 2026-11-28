/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.FTAP.DensityPasting
public import LeanPool.MathFin.Pricing.FTAP.NoArbitrageLocal

/-!
# The Dalang–Morton–Willinger theorem, reduced to its conditional one-period core

The multi-period fundamental theorem of asset pricing on a general probability space with
finitely many assets (`F = EuclideanSpace ℝ (Fin d)`; the reduction and pasting below use only that
`F` is an inner-product space) and a finite horizon: no arbitrage if and only if there is an
equivalent martingale measure. The standard proof (Föllmer–Schied, *Stochastic Finance*, §5.2;
Rogers 1994; Kabanov–Stricker 2001) has three steps. This file assembles the first two with the
third isolated as one precisely stated hypothesis.

1. **Reduction** (`NoArbitrageLocal.lean`): multi-period no arbitrage is equivalent to no
   arbitrage in each one-period market conditional on `𝓕 t` (`noArbitrage_iff_noArbitrageLocal`).
2. **Pasting** (`DensityPasting.lean`): one-period densities `Z t`, `t < T`, with
   `P[Z t | 𝓕 t] = 1` and `P[Z t • S (t+1) | 𝓕 t] = S t` paste to the equivalent martingale
   measure `P.withDensity (∏ Z t)` (`LocalEMMDensities.isEMM_pastedMeasure`).
3. **The conditional one-period FTAP** (not proved here): conditional no arbitrage at period `t`
   produces such a density `Z t` (`HasOnePeriodDensity`). This is the one-period theorem
   `OnePeriodVector.ftap_one_period_vector` (trivial `𝓕 t`) carried out conditionally on `𝓕 t`
   for non-trivial `𝓕 t` on a general space; it needs a measurable selection of the one-period
   equivalent martingale measure over `𝓕 t` (or closedness of the gains cone in `L⁰`). It is
   the hypothesis `ConditionalOnePeriodFTAP` below.

So what is proved is: **assuming** the conditional one-period FTAP for the price `S`, no arbitrage
is equivalent to the existence of an equivalent martingale measure, the measure being the
explicit product `pastedMeasure`. The forward direction (an equivalent martingale measure
precludes arbitrage) is `IsEMM.noArbitrage` and needs no hypothesis. The general-space
Dalang–Morton–Willinger theorem itself, with `ConditionalOnePeriodFTAP` proved rather than
assumed, remains open in this library (issue #313).

## Main definitions

* `HasOnePeriodDensity`: period `t` carries a one-period density (`IsOnePeriodDensity`, defined
  in `DensityPasting.lean`).
* `ConditionalOnePeriodFTAP`: conditional no arbitrage at each period yields a one-period density.

## Main results

* `exists_isEMM_of_hasOnePeriodDensity`: one-period densities in every period give an equivalent
  martingale measure.
* `exists_isEMM_of_noArbitrage_of_conditionalFTAP`: given `ConditionalOnePeriodFTAP`, no
  arbitrage gives an equivalent martingale measure.
* `noArbitrage_iff_exists_isEMM`: given `ConditionalOnePeriodFTAP`, no arbitrage is equivalent
  to the existence of an equivalent martingale measure.

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

fundamental theorem of asset pricing, Dalang–Morton–Willinger, equivalent martingale measure,
no arbitrage, general probability space, conditional one-period market, JEL G13, MSC 91G20,
MSC 60G42
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {𝓕 : Filtration ℕ m0} {P : Measure Ω} {S : ℕ → Ω → F}

/-- **Period `t` carries a one-period density** (`IsOnePeriodDensity`): there is a bounded,
positive, `𝓕 (t+1)`-measurable weight of conditional mean one making `S` a conditional martingale
over `(t, t+1]`. -/
def HasOnePeriodDensity (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (t : ℕ) : Prop :=
  ∃ Z : Ω → ℝ, IsOnePeriodDensity 𝓕 P S t Z

/-- **The conditional one-period FTAP** for the price `S` up to the horizon `T`, as a hypothesis:
conditional no arbitrage at period `t < T` (`NoArbitrageAt`) yields a one-period density
(`HasOnePeriodDensity`). It is the one remaining step of the Dalang–Morton–Willinger theorem on a
general probability space and is **not proved** in this library; it is the conditional version of
`OnePeriodVector.ftap_one_period_vector`, a theorem of the literature for a finite-dimensional `F`
and an adapted integrable price (Föllmer–Schied §5.2). -/
def ConditionalOnePeriodFTAP (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F)
    (T : ℕ) : Prop :=
  ∀ t < T, NoArbitrageAt 𝓕 P S t → HasOnePeriodDensity 𝓕 P S t

variable [IsProbabilityMeasure P] {T : ℕ}

/-- **One-period densities in every period give an equivalent martingale measure**: choosing a
density for each period `t < T` and pasting them (`LocalEMMDensities.isEMM_pastedMeasure`). -/
theorem exists_isEMM_of_hasOnePeriodDensity
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) (hint : ∀ t ≤ T, Integrable (S t) P)
    (hd : ∀ t < T, HasOnePeriodDensity 𝓕 P S t) : ∃ Q, IsEMM 𝓕 P S T Q := by
  choose! Z hZ using hd
  exact ⟨pastedMeasure P Z T, (LocalEMMDensities.mk hS hint hZ).isEMM_pastedMeasure⟩

/-- **Dalang–Morton–Willinger, assuming the conditional one-period FTAP**: for an adapted
integrable price, if the conditional one-period FTAP holds (`ConditionalOnePeriodFTAP`) then no
arbitrage gives an equivalent martingale measure. The reduction
`noArbitrageLocal_of_noArbitrage` turns multi-period no arbitrage into conditional no arbitrage
in each period, the hypothesis produces a density per period, and pasting multiplies them. -/
theorem exists_isEMM_of_noArbitrage_of_conditionalFTAP
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t))
    (hint : ∀ t ≤ T, Integrable (S t) P) (hcond : ConditionalOnePeriodFTAP 𝓕 P S T)
    (hNA : NoArbitrage 𝓕 P S T) : ∃ Q, IsEMM 𝓕 P S T Q :=
  exists_isEMM_of_hasOnePeriodDensity hS hint fun t ht ↦
    hcond t ht (noArbitrageLocal_of_noArbitrage hNA t ht)

/-- **Dalang–Morton–Willinger, assuming the conditional one-period FTAP**: for an adapted
integrable price, if `ConditionalOnePeriodFTAP` holds then no arbitrage is equivalent to the
existence of an equivalent martingale measure. The converse is `IsEMM.noArbitrage`. -/
theorem noArbitrage_iff_exists_isEMM (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t))
    (hint : ∀ t ≤ T, Integrable (S t) P) (hcond : ConditionalOnePeriodFTAP 𝓕 P S T) :
    NoArbitrage 𝓕 P S T ↔ ∃ Q, IsEMM 𝓕 P S T Q :=
  ⟨exists_isEMM_of_noArbitrage_of_conditionalFTAP hS hint hcond, fun ⟨_, hQ⟩ ↦ hQ.noArbitrage⟩

end MathFin
